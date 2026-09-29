/* Prints the 64-bit key (hash with the support in the low 6 bits) of a relabelling SPEC, for mitm KEYA/KEYB.
   usage: relkey SPEC */
#include "ddiff.h"
int main(int argc, char **argv) { int s[52]; parse_rel(argv[1], s); printf("%llx\n", (unsigned long long)((hsh(s) & ~63ull) | support(s))); return 0; }
