struct file_record {
  unsigned int value;
};

struct omitted_file_record {
  unsigned int value;
};

unsigned int file_keep(void) {
  return 6;
}

unsigned int file_drop(void) {
  return 7;
}
