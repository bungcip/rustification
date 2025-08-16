struct S {
  int i;
};

// Exercise an edge case where a struct initializer needs to be in an unsafe
// block
struct fn_ptrs {
  void *v;
  int (*fn1)(void);
  int (*fn2)(int);
};

static const struct S *const global_static_const_ref_struct = &((struct S){.i = 5});
static const char *const global_static_const_literal_str_ptr = "hello";

const struct fn_ptrs fns = {0, 0, 0};
const struct fn_ptrs *p = &fns;


void static_length(){
  (void) global_static_const_ref_struct;
  (void) global_static_const_literal_str_ptr;
  (void) p;
}
