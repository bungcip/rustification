#include <string.h>

static const char digits[] = "0123456789ABCDEF0123456789abcdef";
static const char * const array_of_string[] = {
    "null", "true", "false", "integer", "float", "string", 0
};
  
static const char *const const_string = "hello";

void just_use(){
    (void) digits;
    (void) array_of_string;
    (void) const_string;
}

void static_inside_local_function(){
    static const struct {
        const char *zName;
        const char *zCols;
    } aTable[] = {
        { "a", "ab" },
        { "abc", "abcde" },
    };

    static char * const one[] = { " " };
    static unsigned char *const two[] = {(unsigned char *)"Z"};

    (void) aTable;
    (void) one;
    (void) two;
}
