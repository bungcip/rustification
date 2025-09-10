struct {
  int length;
  unsigned char data[] __attribute__ ((__counted_by__ (length)));
} eed_4;
