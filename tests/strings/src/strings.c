#include <string.h>

int string_length(int buf[4]) {
    const char *empty = "";
    const char *hello_world = "Hello, World!";
    const unsigned char *interior_null = (const unsigned char *) "Hello\0World";

    buf[0] = strlen(empty);
    buf[1] = strlen(hello_world);
    buf[2] = strlen(interior_null);
    buf[3] = strlen("literal");

    int length = buf[0] + buf[1] + buf[2] + buf[3];
    return length;
}

int mutable_string_array(){
    char *buffer[4];
    
    const char *filename = "123456";

    buffer[0] = 0;
    buffer[1] = filename;
    buffer[2] = filename;
    buffer[3] = 0;

    return strlen(buffer[2]);
}

int const_string_array(){
    // from sqlite
    const char *azOpt[] = {"_ROWID_", "ROWID", "OID"};

    return strlen(azOpt[1]);
}