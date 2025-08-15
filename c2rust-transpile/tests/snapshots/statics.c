struct S {
  int i;
};

static const struct S *const global_static_const_ref_struct = &((struct S){.i = 5});
static const char *const global_static_const_literal_str_ptr = "hello";

void static_length(){
  (void) global_static_const_ref_struct;
  (void) global_static_const_literal_str_ptr;
}
