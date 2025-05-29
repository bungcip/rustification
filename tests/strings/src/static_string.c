#include <string.h>

static const char digits[] = "0123456789ABCDEF0123456789abcdef";
static const char * const array_of_string[] = {
    "null", "true", "false", "integer", "float", "string", 0
};
  
int static_length(){
    // calling strlen on a null pointer is undefined behavior, so we just check if it is null
    int is_null = array_of_string[6] == 0; 
    return 
           is_null +
           strlen(digits) + 
           strlen(array_of_string[0]) + strlen(array_of_string[1]) +
           strlen(array_of_string[2]) + strlen(array_of_string[3]) +
           strlen(array_of_string[4]) + strlen(array_of_string[5]);
}

int static_inside_local_function(){
    // from sqlite 
    static const struct {
        const char *zName;
        const char *zCols;
    } aTable[] = {
        { "a", "ab" },
        { "abc", "abcde" },
    };

    static char * const one[] = { " " };
    static unsigned char *const two[] = {(unsigned char *)"Z"};

    return strlen(aTable[0].zName) + strlen(aTable[0].zCols) +
           strlen(aTable[1].zName) + strlen(aTable[1].zCols) + 
           strlen(one[0]) + strlen(two[0]);

}
