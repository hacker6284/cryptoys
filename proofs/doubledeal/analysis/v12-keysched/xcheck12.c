#include <stdio.h>
#include "dd12.h"
/* reads lines: 52 ints deck; prints passkey12(deck) and unkeyed(deck) and full v12 encrypt with key=deck of msg=identity */
int main(void) { int d[52];
  while (1) { for (int i = 0; i < 52; i++) if (scanf("%d", &d[i]) != 1) return 0;
    int o[52], u[52], keys[7][52], c[52], m[52];
    passkey12(d, o); for (int i = 0; i < 52; i++) printf("%d ", o[i]); printf("\n");
    unkeyed(d, u); for (int i = 0; i < 52; i++) printf("%d ", u[i]); printf("\n");
    memcpy(keys[0], d, sizeof d); for (int r = 1; r <= 6; r++) passkey12(keys[r-1], keys[r]);
    for (int i = 0; i < 52; i++) m[i] = i; encrypt_keys(m, keys, c, 0);
    for (int i = 0; i < 52; i++) printf("%d ", c[i]); printf("\n"); } }
