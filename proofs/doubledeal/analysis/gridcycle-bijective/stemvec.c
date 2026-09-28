/* prints N (input, stem(input)) pairs for xcheck.py */
#include <stdio.h>
#include <stdlib.h>
#include "layers.h"
int main(int argc, char **argv) { (void)argc; long N = atol(argv[1]); uint64_t s = 12345; int d[52], o[52];
    for (long n = 0; n < N; n++) { shuffle_(d, &s); stem(d, o);
        for (int i = 0; i < 52; i++) printf("%d%c", d[i], i < 51 ? 0x2c : 0x20);
        for (int i = 0; i < 52; i++) printf("%d%c", o[i], i < 51 ? 0x2c : 0x0a); }
    return 0; }
