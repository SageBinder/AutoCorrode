/* SPDX-License-Identifier: MIT */
struct kept_record { unsigned int value; };
struct dropped_record { unsigned int value; };

unsigned int kept(unsigned int x) { return x + 1; }
unsigned int dropped(unsigned int x) { return x + 2; }
unsigned int read_record(struct kept_record *p) { return p->value; }
