struct AnonymousEnumInStruct
{
    enum
    {
        VALUE1,
        VALUE2
    };
};

struct NestedStructInStruct
{
    struct StructInsider
    {
        int yup;
    };
};

struct AnonymousStructInStruct
{
    struct
    {
        int some_number;
    } member;
};

union AnonymousEnumInUnion
{
    enum
    {
        VALUE3,
        VALUE4
    };
    int a;
};

union AnonymousStructInUnion
{
    struct
    {
        unsigned int low;
        unsigned int high;
    } number;
    int a;
};

union NestedStructInUnion
{
    struct UnionInsider
    {
        int yup;
    };
    int a;
};

void struct_declaration()
{
    int value = VALUE2;
    struct AnonymousEnumInStruct a;
    struct AnonymousStructInStruct b;
    struct NestedStructInStruct c;
    struct StructInsider d;
}

void union_declaration()
{
    int value = VALUE4;
    union AnonymousEnumInUnion a;
    union AnonymousStructInUnion b;
    union NestedStructInUnion c;
    struct UnionInsider d;
}