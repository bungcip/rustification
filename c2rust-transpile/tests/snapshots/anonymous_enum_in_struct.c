struct A {
    enum {
        VALUE1,
        VALUE2
    };
};

void use_variant_of_anonymous_enum() {
    int value = VALUE2;
}
