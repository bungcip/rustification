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

const struct fn_ptrs fns = {0, 0, 0};
const struct fn_ptrs *p = &fns;

static int other_c_to_i(char c) {
  int *null_var = 0;
  return (int) c;
}

int (*global_fn)(char) = other_c_to_i;

// from sqlite3
typedef struct sqlite3_mutex sqlite3_mutex;
static sqlite3_mutex *unixBigLock = 0;

void static_length(){
  (void) global_static_const_ref_struct;
  (void) p;
  (void) global_fn;
  (void) unixBigLock;
}
