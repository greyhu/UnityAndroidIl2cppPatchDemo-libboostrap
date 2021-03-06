#ifndef SHADOW_ZIP_H
#define SHADOW_ZIP_H

#include <map>
#include <vector>
#include <string>
#include <stdint.h>
#include <stdio.h>
#include "singleton.hpp"

struct FilePartitionInfo
{
    FilePartitionInfo(uint64_t _shadow_start, uint64_t _shadow_stop, int _file_index, uint64_t _start_in_file, uint64_t _stop_in_file)
        : shadow_start_(_shadow_start), shadow_stop_(_shadow_stop), file_index_(_file_index),
        start_in_file_(_start_in_file), stop_in_file_(_stop_in_file)
    {}
    //[shadow_start_, shadow_stop_)
    uint64_t shadow_start_;
    uint64_t shadow_stop_;

    int file_index_;
    uint64_t start_in_file_;
    uint64_t stop_in_file_;
};

namespace android {
	class ZipEntry;
}
class VirtualZipFile {
public:
	int real_file_index;
	uint64_t end_of_file_;
	std::vector<android::ZipEntry*> all_entries;
	std::vector<FilePartitionInfo> patch_partitions;
	void WriteHeader(char* path, int header_data_index);
	void AddEntries(std::vector<android::ZipEntry*>* entries, std::map<std::string, android::ZipEntry*>* filename_2_entry);

	int pre_file_index = -1;
	uint64_t pre_file_stop = 0;
	uint64_t pre_shadow_stop = 0;
};

class ShadowZip
{
public:
    ShadowZip()
    {
	}
    virtual ~ShadowZip(){
        fclose(NULL);
    }

    FILE* fopen(const char* path);
    off64_t fseek(FILE *stream, off64_t offset, int whence);
    long ftell(FILE *stream);
    void rewind(FILE *stream);
    size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);
	char* fgets(char *s, int size, FILE *stream);
    int fclose(FILE* _fp);

    static int init(const char* _patch_dir, const char* _sys_apk_file, const char* _obb_file_path);
	static uint64_t get_eof_pos(const char* path);
	void output_apk(const char* _apk_path, const char* _patch_dir);
    static FILE *(*volatile old_fopen)(const char *path, const char *mode);
    static int (*volatile old_fseek)(FILE *stream, long offset, int whence);
    static long (*volatile old_ftell)(FILE *stream);
    //static void (*volatile old_rewind)(FILE *stream);
    static size_t (*volatile old_fread)(void *ptr, size_t size, size_t nmemb, FILE *stream);
	static char* (*volatile old_fgets)(char *s, int size, FILE *stream);
    static int (*volatile old_fclose)(FILE* _fp);

	static bool contains_path(const char* _apk_file, const char* _check_path);
private:
    FILE* prepare_file(int _file_index);
	VirtualZipFile* virtualFile;

private:
    int64_t pos_;
    std::vector<FILE *> fp_array_;
};

#endif /* SHADOW_ZIP_H */
