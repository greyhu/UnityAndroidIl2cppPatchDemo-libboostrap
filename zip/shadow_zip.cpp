#include "shadow_zip.h"
#include "log.h"
#include "ZipFile.h"
#include "ZipEntry.h"
#include <sys/types.h>
#include <dirent.h>
#include <assert.h>
#include <memory>
#include <string.h>

using namespace android;
static void add_entry_to_partition(ZipEntry* entry,
	int& pre_file_index,
	uint64_t& pre_file_stop,
	uint64_t& pre_shadow_stop,
	VirtualZipFile *vfile);

static bool IsObbPatch(const char* path) {
	int obb_ext_len = 9;//strlen(".obbpatch");
	int pathlen = strlen(path);
	bool isobb = false;
	if (pathlen > obb_ext_len && memcmp(path + pathlen - obb_ext_len, ".obbpatch", obb_ext_len) == 0) {
		isobb = true;
	}
	return isobb;
}

struct ShadowZipGlobalData
{
	bool hasObbFile;
	std::map<std::string, VirtualZipFile*> all_virtual_files_;
    std::vector<std::string> all_files_;
};

void VirtualZipFile::WriteHeader(char* path, int header_data_index) {
	MY_LOG("header file path=%s", path);
	FILE* end_patch_file = ::fopen(path, "wb");
	for (int i = 0; i < all_entries.size(); i++) {
		ZipEntry* entry = all_entries[i];
		MY_LOG("%s, method:%d, LFHOffset:%08lx", entry->getFileName(), entry->mCDE.mCompressionMethod, entry->getLFHOffset());
		entry->mCDE.write(end_patch_file);
	}
	EndOfCentralDir end_of_cd;
	end_of_cd.mNumEntries = all_entries.size();
	end_of_cd.mTotalNumEntries = all_entries.size();
	end_of_cd.mCentralDirSize = ::ftell(end_patch_file);
	end_of_cd.mCentralDirOffset = pre_shadow_stop;
	end_of_cd.write(end_patch_file);
	uint64_t end_size = ::ftell(end_patch_file);
	::fclose(end_patch_file);

	end_of_file_ = pre_shadow_stop + end_size;
	FilePartitionInfo partition(pre_shadow_stop, pre_shadow_stop + end_size, header_data_index, 0, end_size);
	patch_partitions.push_back(partition);
}

void VirtualZipFile::AddEntries(std::vector<ZipEntry*>* entries, std::map<std::string, ZipEntry*>* filename_2_entry) {
	for (int i = 0; i < entries->size(); i++)
	{
		ZipEntry* entry = (*entries)[i];
		std::string name(entry->getFileName());
		MY_LOG("entry %s", name.c_str());
		std::map<std::string, ZipEntry*>::iterator it = filename_2_entry->find(name);
		if (it != filename_2_entry->end()) {	//如果在补丁中存在
			MY_LOG("replace this entry");
			entry = it->second;	//替换掉
		}
		entry->mUserData2 = 1;	//标记为已处理过
		uint64_t entry_new_start = pre_shadow_stop;
		add_entry_to_partition(entry, pre_file_index, pre_file_stop, pre_shadow_stop, this);
		entry->setLFHOffset((off_t)entry_new_start);
		all_entries.push_back(entry);	//加进去
	}
}

#define g_shadowzip_global_data (LeakSingleton<ShadowZipGlobalData, 0>::instance())

FILE *(*volatile ShadowZip::old_fopen)(const char *path, const char *mode);
int (*volatile ShadowZip::old_fseek)(FILE *stream, long offset, int whence);
long (*volatile ShadowZip::old_ftell)(FILE *stream);
//void (*volatile ShadowZip::old_rewind)(FILE *stream);
size_t (*volatile ShadowZip::old_fread)(void *ptr, size_t size, size_t nmemb, FILE *stream);
char* (*volatile ShadowZip::old_fgets)(char *s, int size, FILE *stream);
int (*volatile ShadowZip::old_fclose)(FILE* _fp);

static void get_files(const char* _apk_patch_path)
{
	std::vector<std::string>& _files = g_shadowzip_global_data->all_files_;
    DIR* dir = opendir(_apk_patch_path);
    if (dir == NULL){ 
		MY_INFO("opendir failed:%d[%s]", errno, _apk_patch_path);
		return; 
	}

    struct dirent *ent = NULL;
    while((ent = readdir(dir)) != NULL) {
        if(ent->d_type & DT_REG) {  
			std::string patch_file = std::string(_apk_patch_path) + "/" + ent->d_name;
			if (!IsObbPatch(patch_file.c_str()) || g_shadowzip_global_data->hasObbFile) {
				_files.push_back(patch_file);
				MY_INFO("patch file:[%s]", patch_file.c_str());
			}
        }
    }
    closedir(dir);
}

static int parse_apk(const char* _path, std::vector<ZipEntry*>& _all_entries, int file_index)
{
    off_t fileLength, seekStart;
    long readAmount;
    int i;
    EndOfCentralDir endOfCentralDir;

    FILE *fp = fopen(_path, "rb");
	if (fp == NULL){
		MY_ERROR("failure parse file %s", _path);
        return -1;
	}
	std::shared_ptr<FILE> autoDel(fp, [](FILE* fp){::fclose(fp);});
	
    fseek(fp, 0, SEEK_END);
    fileLength = ftell(fp);
    rewind(fp);

    /* too small to be a ZIP archive? */
    if (fileLength < EndOfCentralDir::kEOCDLen) {
        MY_ERROR("%s len is too small\n", _path);
        return -1;
    }

    unsigned char* buf = new unsigned char[EndOfCentralDir::kMaxEOCDSearch];
    if (buf == NULL) {
        MY_ERROR("failure allocating %d bytes", EndOfCentralDir::kMaxEOCDSearch);
        return -1;
    }

    if (fileLength > EndOfCentralDir::kMaxEOCDSearch) {
        seekStart = fileLength - EndOfCentralDir::kMaxEOCDSearch;
        readAmount = EndOfCentralDir::kMaxEOCDSearch;
    } else {
        seekStart = 0;
        readAmount = (long) fileLength;
    }
    if (fseek(fp, seekStart, SEEK_SET) != 0) {
        MY_ERROR("failure seeking to end of zip at %ld", (long) seekStart);
        delete[] buf;
        return -1;
    }

    /* read the last part of the file into the buffer */
    if (fread(buf, 1, readAmount, fp) != (size_t) readAmount) {
        MY_ERROR("read error! wanted %ld\n", readAmount);
        delete[] buf;
        return -1;
    }

    /* find the end-of-central-dir magic */
    for (i = readAmount - 4; i >= 0; i--) {
        if (buf[i] == 0x50 && ZipEntry::getLongLE(&buf[i]) == EndOfCentralDir::kSignature) {
            break;
        }
    }
    if (i < 0) {
        MY_ERROR("not zip:%s\n", _path);
        delete[] buf;
        return -1;
    }

    /* extract eocd values */
    int result = endOfCentralDir.readBuf(buf + i, readAmount - i);
    if (result != NO_ERROR) {
        MY_ERROR("failure reading %ld bytes for end of centoral dir", readAmount - i);
        delete[] buf;
        return -1;
    }
    //endOfCentralDir.dump();

    if (endOfCentralDir.mDiskNumber != 0 || endOfCentralDir.mDiskWithCentralDir != 0 ||
        endOfCentralDir.mNumEntries != endOfCentralDir.mTotalNumEntries)
    {
        MY_ERROR("archive spanning not supported\n");
        delete[] buf;
        return -1;
    }

    /*
     * So far so good.  "mCentralDirSize" is the size in bytes of the
     * central directory, so we can just seek back that far to find it.
     * We can also seek forward mCentralDirOffset bytes from the
     * start of the file.
     *
     * We're not guaranteed to have the rest of the central dir in the
     * buffer, nor are we guaranteed that the central dir will have any
     * sort of convenient size.  We need to skip to the start of it and
     * read the header, then the other goodies.
     *
     * The only thing we really need right now is the file comment, which
     * we're hoping to preserve.
     */
    if (fseek(fp, endOfCentralDir.mCentralDirOffset, SEEK_SET) != 0) {
        MY_ERROR("failure seeking to central dir offset %ld\n", endOfCentralDir.mCentralDirOffset);
        delete[] buf;
        return -1;
    }

    /*
     * Loop through and read the central dir entries.
     */
    int entry;
    for (entry = 0; entry < endOfCentralDir.mTotalNumEntries; entry++) {
        ZipEntry* pEntry = new ZipEntry;

        result = pEntry->initFromCDE(fp);
        if (result != NO_ERROR) {
            MY_ERROR("initFromCDE failed\n");
            delete pEntry;
            delete[] buf;
            return -1;
        }
		pEntry->mUserData1 = file_index;
        _all_entries.push_back(pEntry);
    }

    /*
     * If all went well, we should now be back at the EOCD.
     */
    {
        unsigned char checkBuf[4];
        if (fread(checkBuf, 1, 4, fp) != 4) {
            MY_ERROR("EOCD check read failed");
            delete[] buf;
            return -1;
        }
        if (ZipEntry::getLongLE(checkBuf) != EndOfCentralDir::kSignature) {
            MY_ERROR("EOCD read check failed");
            delete[] buf;
            return -1;
        }
    }
    return 0;
}

void clean_file_entries_map(std::vector<std::vector<ZipEntry*> > & _entries_in_zip_file)
{
    std::vector<std::vector<ZipEntry*> >::iterator it = _entries_in_zip_file.begin();
    for(; it != _entries_in_zip_file.end(); it++)
    {
        std::vector<ZipEntry*>& entries = *it;
        for(int i = 0; i < entries.size(); i++) {
            delete entries[i];
        }
        entries.clear();
    }
    _entries_in_zip_file.clear();
}

static void add_entry_to_partition(ZipEntry* entry, 
    int& pre_file_index,
    uint64_t& pre_file_stop,
    uint64_t& pre_shadow_stop,
    VirtualZipFile *vfile)
{
    int file_index = entry->mUserData1;
    uint64_t file_start = entry->getEntryBegin();	//真正文件的start位置
    bool can_merge = (file_index == pre_file_index) && ( file_start == pre_file_stop );	//同一个真实文件（apk或zip）

    pre_file_index = file_index;
    pre_file_stop = entry->getEntryEnd(); //真正文件的stop位置
    int32_t entry_size = pre_file_stop - file_start;	//真正文件的大小（zip中）

	int shadow_start = pre_shadow_stop;
	int shadow_stop = shadow_start + entry_size;
	pre_shadow_stop = shadow_stop; //这个是一直往后加的
    if (can_merge)
    {//FilePartitionInfo 是一个连续的段
        FilePartitionInfo& partition = vfile->patch_partitions.back();
        partition.shadow_stop_ += entry_size;
        partition.stop_in_file_ += entry_size;
    }
    else{
		//新的文件片段
        FilePartitionInfo partition(shadow_start, shadow_stop, file_index, file_start, pre_file_stop);
		vfile->patch_partitions.push_back(partition);
    }
}

void ShadowZip::output_apk(const char* _apk_path, const char* _patch_dir)
{
	ShadowZip test;
    FILE* fr = test.fopen(_apk_path);
	
    char test_apk_path[512] = {0};
    snprintf( test_apk_path, sizeof(test_apk_path), "%s/test.apk", _patch_dir );
    FILE* fw = old_fopen( test_apk_path, "wb" );
    char buffer[1024] = {0};
    while(1)
    {
        int read_cnt = test.fread( buffer, 1, sizeof(buffer), fr );
        if (read_cnt <= 0){break;}
        int write_cnt = fwrite( buffer, 1, read_cnt, fw );
        if (write_cnt != read_cnt )
        {
            MY_LOG("write error %d != %d", write_cnt, read_cnt);
            break;
        }
    }
    MY_LOG("copy end at %ld, %llu", old_ftell(fw), (unsigned long long)virtualFile->end_of_file_);
    test.fclose(fr);
    old_fclose(fw);
}

int ShadowZip::init(const char* _patch_dir, const char* _sys_apk_file, const char* _obb_file_path)
{	
	LeakSingleton<ShadowZipGlobalData, 0>::init();
	g_shadowzip_global_data->hasObbFile = (strcmp(_obb_file_path, "") != 0);
	if (g_shadowzip_global_data->hasObbFile) {
		MY_INFO("hasObbFile");
	}
	else {
		MY_INFO("no ObbFile");
	}
    old_fopen = NULL;
    old_fseek = NULL;
    old_ftell = NULL;
    //old_rewind = NULL;
    old_fread = NULL;
	old_fgets = NULL;
    old_fclose = NULL;
    g_shadowzip_global_data->all_virtual_files_.clear();
    g_shadowzip_global_data->all_files_.clear();
    g_shadowzip_global_data->all_files_.push_back(_sys_apk_file);

    //find all patch files
    char apk_patch_path[512] = {0};
    snprintf( apk_patch_path, sizeof(apk_patch_path), "%s/assets_bin_Data", _patch_dir );
    get_files( apk_patch_path );	//扫描所有补丁zip文件追加到all_files_
    if( g_shadowzip_global_data->all_files_.size() <= 1 ){
        MY_INFO("no apk patches:[%s/assets_bin_Data]", _patch_dir);
        return -1;
    }

    //find all entries in patches
    std::vector<std::vector<ZipEntry*> > entries_in_zip_file(g_shadowzip_global_data->all_files_.size());
    std::map<std::string, ZipEntry*> filename_2_entry_apk;
	std::map<std::string, ZipEntry*> filename_2_entry_obb;
    for(int i = 1; i < g_shadowzip_global_data->all_files_.size(); i++) {
        std::string& zip_path = g_shadowzip_global_data->all_files_[i];
		bool isobb = IsObbPatch(zip_path.c_str());

        std::vector<ZipEntry*> zip_entries;
        int ret = parse_apk(zip_path.c_str(), zip_entries, i);
        entries_in_zip_file[i] = zip_entries;
        if (ret != 0){
            MY_ERROR("parse file failed:%s", zip_path.c_str());
            clean_file_entries_map(entries_in_zip_file);
            return -1;
        }
        for(int j = 0; j < zip_entries.size(); j++)
        {
            ZipEntry* entry = zip_entries[j];
            entry->mUserData1 = i;
            std::string filename = entry->getFileName();
			if (filename.at(filename.length() - 1) == '/') { continue; }
            MY_LOG("find patch:%s in %s", filename.c_str(), zip_path.c_str());
			if (isobb) {
				if (filename_2_entry_obb.find(filename) != filename_2_entry_obb.end()) {
					MY_ERROR("dup obb patch file failed:%s", filename.c_str());
					clean_file_entries_map(entries_in_zip_file);
					return -1;
				}
				filename_2_entry_obb[filename] = entry;
			}
			else {
				if (filename_2_entry_apk.find(filename) != filename_2_entry_apk.end()) {
					MY_ERROR("dup apk patch file failed:%s", filename.c_str());
					clean_file_entries_map(entries_in_zip_file);
					return -1;
				}
				filename_2_entry_apk[filename] = entry;
			}  
        }
    }

    // find all entries in apk，先把所有的apk entry加进去
    std::vector<ZipEntry*> apk_entries;
    int ret = parse_apk(_sys_apk_file, apk_entries, 0);
    entries_in_zip_file[0] = apk_entries;
    if (ret != 0){
        MY_ERROR("parse apk file failed:%s", _sys_apk_file);
        clean_file_entries_map(entries_in_zip_file);
        return -1;
    }

	//entries partition
	VirtualZipFile* vfile_apk = new VirtualZipFile();
	g_shadowzip_global_data->all_virtual_files_[std::string(_sys_apk_file)] = vfile_apk;
	vfile_apk->AddEntries(&apk_entries, &filename_2_entry_apk);

	VirtualZipFile* vfile_obb = NULL;
	std::vector<ZipEntry*> obb_entries;
	if (g_shadowzip_global_data->hasObbFile) {
		//把所有的obb entry加进去
		g_shadowzip_global_data->all_files_.push_back(_obb_file_path);
		ret = parse_apk(_obb_file_path, obb_entries, g_shadowzip_global_data->all_files_.size() - 1);
		if (ret != 0) {
			MY_ERROR("parse obb file failed:%s", _obb_file_path);
			clean_file_entries_map(entries_in_zip_file);
			return -1;
		}
		vfile_obb = new VirtualZipFile();
		g_shadowzip_global_data->all_virtual_files_[std::string(_obb_file_path)] = vfile_obb;
		vfile_obb->AddEntries(&obb_entries, &filename_2_entry_obb);
	}
	
    for(int i = 1; i < entries_in_zip_file.size(); i++)
    {//再处理更新zip文件里面的
        std::vector<ZipEntry*>& entries = entries_in_zip_file[i];
        for(int j = 0; j < entries.size(); j++) {
            ZipEntry* entry = entries[j];
            if (entry->mUserData2 != 0) continue;	//在处理apk，obb的时候已处理了，跳过
			uint64_t entry_new_start = 0;;
			if (IsObbPatch(g_shadowzip_global_data->all_files_[i].c_str())) {
				if (vfile_obb != NULL) {
					entry_new_start = vfile_obb->pre_shadow_stop;
					add_entry_to_partition(entry, vfile_obb->pre_file_index, vfile_obb->pre_file_stop, vfile_obb->pre_shadow_stop, vfile_obb);
					vfile_obb->all_entries.push_back(entry);	//加进去
				}
			}
			else {
				entry_new_start = vfile_apk->pre_shadow_stop;
				add_entry_to_partition(entry, vfile_apk->pre_file_index, vfile_apk->pre_file_stop, vfile_apk->pre_shadow_stop, vfile_apk);
				vfile_apk->all_entries.push_back(entry);	//加进去
			}
            entry->setLFHOffset((off_t)entry_new_start);
        }
    }
    
    char end_patch_path[512] = {0};
    snprintf( end_patch_path, sizeof(end_patch_path), "%s/.patch.data", _patch_dir );
    g_shadowzip_global_data->all_files_.push_back(end_patch_path);
	int header_data_index = g_shadowzip_global_data->all_files_.size() - 1;
	vfile_apk->WriteHeader(end_patch_path, header_data_index);

	if (vfile_obb != NULL) {
		char end_patch_path_obb[512] = { 0 };
		snprintf(end_patch_path_obb, sizeof(end_patch_path_obb), "%s/.obbpatch.data", _patch_dir);
		g_shadowzip_global_data->all_files_.push_back(end_patch_path_obb);
		header_data_index = g_shadowzip_global_data->all_files_.size() - 1;
		vfile_obb->WriteHeader(end_patch_path_obb, header_data_index);
	}

	//for (auto it = g_shadowzip_global_data->all_virtual_files_.begin();it != g_shadowzip_global_data->all_virtual_files_.end();++it) {
	//	for (int i = 0; i < it->second->patch_partitions.size(); i++)
	//	{
	//		FilePartitionInfo& partition = it->second->patch_partitions[i];
	//		MY_LOG("0x%08llx - 0x%08llx file:%d, [0x%08llx - 0x%08llx] ",
	//			(unsigned long long)partition.shadow_start_,
	//			(unsigned long long)partition.shadow_stop_,
	//			partition.file_index_,
	//			(unsigned long long)partition.start_in_file_,
	//			(unsigned long long)partition.stop_in_file_);
	//	}
	//}
    clean_file_entries_map(entries_in_zip_file);
	
    return 0;
}

uint64_t ShadowZip::get_eof_pos(const char* path)
{
	auto itfile = g_shadowzip_global_data->all_virtual_files_.find(std::string(path));
	if (itfile == g_shadowzip_global_data->all_virtual_files_.end()) {
		return 0;
	}
	MY_METHOD("get_eof_pos -> 0x%08llx", (unsigned long long)itfile->second->end_of_file_);
	return itfile->second->end_of_file_;
}

FILE* ShadowZip::fopen(const char* path)
{
	//fopen事实上只会用于apk和obb
	MY_LOG("ShadowZip::fopen");
    pos_ = 0;
	//fp_array_.clear();
	int file_index = -1;
	for(int i = 0; i < g_shadowzip_global_data->all_files_.size(); i++)
	{
		if (fp_array_.size() < g_shadowzip_global_data->all_files_.size()) {
			fp_array_.push_back(NULL);
		}
		//其实那些zip文件都会被跳过
		if (strcmp(g_shadowzip_global_data->all_files_[i].c_str(), path) == 0) {
			file_index = i;
		}
	}
	if (file_index == -1) {
		MY_ERROR("can not find path:%s", path);
		return NULL;
	}
    FILE* fp = prepare_file(file_index);
	MY_METHOD("fopen -> 0x%08zx", (size_t)fp);
	auto it = g_shadowzip_global_data->all_virtual_files_.find(std::string(path));
	if (it != g_shadowzip_global_data->all_virtual_files_.end()) {
		virtualFile = it->second;
	}
	return fp;
}

off64_t ShadowZip::fseek(FILE *stream, off64_t offset, int whence)
{	
	MY_METHOD("fseek -> 0x%08zx at 0x%08llx with type %d", (size_t)stream, (unsigned long long)offset, whence);
    int64_t cur_pos = pos_;
    if (whence == SEEK_SET){
        pos_ = offset;
    }
    else if (whence == SEEK_CUR){
        pos_ += offset;
    }
    else if (whence == SEEK_END){
        pos_ = virtualFile->end_of_file_ + offset;
    }
    if (pos_ < 0 || pos_ > virtualFile->end_of_file_){
        pos_ = cur_pos;
        return -1;
    }
    return 0;
}

long ShadowZip::ftell(FILE *stream)
{
	//MY_METHOD("ftell -> 0x%08zx at 0x%08llx", (size_t)stream, (unsigned long long)pos_);
    return (long) pos_;
}

void ShadowZip::rewind(FILE *stream)
{
    pos_ = 0;
}

size_t ShadowZip::fread(void *ptr, size_t size, size_t nmemb, FILE *stream)
{
	MY_METHOD("fread -> 0x%08zx at 0x%08llx, size:%zu, n:%zu", (size_t)stream, (unsigned long long)pos_, size, nmemb);
	if (((int)nmemb) <= 0){return 0;}
	
    uint64_t begin = pos_;	//虚拟文件中的beginpos
    uint64_t end = pos_ + size * nmemb;	//虚拟文件中的endpos
    size_t ret = 0;
	
    void* write_ptr = ptr;
	//patch_partitions 是顺序的，找到第一个即可
    for(int i = 0; i < virtualFile->patch_partitions.size(); i++)
    {
        FilePartitionInfo& partitionInfo = virtualFile->patch_partitions[i];
        if (begin >= partitionInfo.shadow_stop_){	//往后跳
            continue;
        }
        assert(begin >= partitionInfo.shadow_start_);

        uint64_t start_in_file = begin - partitionInfo.shadow_start_ + partitionInfo.start_in_file_;	//片段在真实文件中的起始位置
        uint64_t stop_in_file = (end >= partitionInfo.shadow_stop_) ? partitionInfo.stop_in_file_ : (end - partitionInfo.shadow_start_ + partitionInfo.start_in_file_);	//片段在真实文件中的结束位置
        int64_t read_size = stop_in_file - start_in_file;	//整个片段长度
        if (read_size > nmemb){
            MY_LOG("partition:%d, offset:[%zx,%zx), partition_size:%zu", i, (size_t)start_in_file, (size_t)stop_in_file,  (size_t)read_size);
            MY_LOG("shadow:[%zx,%zx) pos:%zx", (size_t)begin, (size_t)end, (size_t)pos_);
		}
		//去打开真正的文件
        FILE* fp = prepare_file(partitionInfo.file_index_);
        assert(fp != NULL);
		//跳到对应的偏移
        old_fseek(fp, start_in_file, SEEK_SET);
		//读取整个片段
        old_fread(write_ptr, 1, read_size, fp);
        ret += read_size;
        pos_ += read_size;
        write_ptr = (char*)write_ptr + read_size;
        begin += read_size;	//读完之后的位置
        if (begin >= end){	//读够足够的数据了
			return ret;	//返回
		}
		//没读够，继续下一个片段
    }
    return ret;

}

char* ShadowZip::fgets(char *s, int size, FILE *stream)
{
	//MY_METHOD("fgets -> 0x%08zx at 0x%08llx, size:%d", (size_t)stream, (unsigned long long)pos_, size);
    uint64_t begin = pos_;
    uint64_t end = pos_ + size;

    void* write_ptr = s;
    for(int i = 0; i < virtualFile->patch_partitions.size(); i++)
    {
        FilePartitionInfo& info = virtualFile->patch_partitions[i];
        if (begin >= info.shadow_stop_){
            continue;
        }
        assert(begin >= info.shadow_start_);

        uint64_t start_in_file = begin - info.shadow_start_ + info.start_in_file_;
        uint64_t stop_in_file = (end >= info.shadow_stop_) ? info.stop_in_file_ : (end - info.shadow_start_ + info.start_in_file_);
        int64_t read_size = stop_in_file - start_in_file;
        if (read_size > size){
            MY_LOG("partition:%d, offset:[%zx,%zx) read size:%zu", i, (size_t)start_in_file, (size_t)stop_in_file,  (size_t)read_size);
            MY_LOG("shadow:[%zx,%zx) pos:%zx", (size_t)begin, (size_t)end, (size_t)pos_);
        }
        FILE* fp = prepare_file(info.file_index_);
        assert(fp != NULL);
        old_fseek(fp, start_in_file, SEEK_SET);
        char* ret = old_fgets(s, size, fp); 
		long pos_after_fgets = old_ftell(fp);
		read_size = pos_after_fgets - start_in_file;
        pos_ += read_size;
        write_ptr = (char*)write_ptr + read_size;
        begin += read_size;
        return ret;
    }
    return NULL;
}

int ShadowZip::fclose(FILE* stream)
{
	MY_METHOD("fclose -> 0x%08zx at 0x%08llx", (size_t)stream, (unsigned long long)pos_);
    for(int i = 0; i < fp_array_.size(); i++) 
    {
		FILE* fp = fp_array_[i];
		if (fp) {		
			MY_METHOD("fclose -> 0x%08zx fp%d at 0x%08lx", (size_t)stream, i, old_ftell(fp));
			old_fclose(fp);
			fp_array_[i] = NULL;
		}
    }
    //fp_array_.clear();
    return 0;
}

bool ShadowZip::contains_path(const char* _apk_file, const char* _check_path)
{
	bool ret = false;
	std::vector<ZipEntry*> zip_entries;
	if (parse_apk(_apk_file, zip_entries, 0) != 0){
		MY_ERROR("parse file failed:%s", _apk_file);
		return ret;
	}
	for(int j = 0; j < zip_entries.size(); j++)
	{
		ZipEntry* entry = zip_entries[j];
		std::string filename = entry->getFileName();
		if (memcmp(filename.c_str(), _check_path, strlen(_check_path)) == 0){
			ret = true;
			break;
		}
	}
	
	for(int i = 0; i < zip_entries.size(); i++) {
        delete zip_entries[i];
	}
	zip_entries.clear();
	
	MY_INFO("%s%s contains path:%s", _apk_file, ret ? "": " doesn't", _check_path);
	return ret;
}

FILE* ShadowZip::prepare_file(int _file_index)
{
	//prepare里面打开真正的文件，zip，apk，obb
    if (fp_array_[_file_index] != NULL ){
        return fp_array_[_file_index];
    }
	
	//incace of too many file opened, close all except base.apk
	//for(int i = 1; i < fp_array_.size(); i++) 
 //   {
	//	FILE* fp = fp_array_[i];
	//	if (fp) {		
	//		MY_METHOD("fclose -> 0x%08zx fp:%d at 0x%08lx", (size_t)fp, i, old_ftell(fp));
	//		old_fclose(fp);
	//		fp_array_[i] = NULL;
	//	}
 //   }

    std::string& path = g_shadowzip_global_data->all_files_[_file_index];
    FILE* fp = old_fopen(path.c_str(), "rb");
    if (fp == NULL) {
        MY_LOG("can't open file:%s", path.c_str());
        return NULL; 
    }
	MY_METHOD("prepare_file %s -> 0x%08zx", path.c_str(), (size_t)fp);
    fp_array_[_file_index] = fp;
    return fp;
}
