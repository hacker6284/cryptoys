/* Pollard rho (Floyd, 3-way partition) for the T2 group: p = 3^35 - 3^29 - 1, g = 3 of prime order q.
   usage: break_t2 p q A   -> prints x with 3^x = A (mod p).  Demonstrates that T2 is broken. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static u64 P, Q, G = 3, H;
static u64 mulm(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }
static u64 powm(u64 b, u64 e, u64 m) { u64 r = 1; while (e) { if (e & 1) r = mulm(r, b, m); b = mulm(b, b, m); e >>= 1; } return r; }
static void step(u64 *x, u64 *a, u64 *b) {
  switch (*x % 3) {
    case 0: *x = mulm(*x, G, P); *a = (*a + 1) % Q; break;
    case 1: *x = mulm(*x, *x, P); *a = (*a * 2) % Q; *b = (*b * 2) % Q; break;
    default: *x = mulm(*x, H, P); *b = (*b + 1) % Q; break;
  }
}
int main(int argc, char **argv) {
  P = strtoull(argv[1], 0, 10); Q = strtoull(argv[2], 0, 10); H = strtoull(argv[3], 0, 10);
  for (u64 seed = 1;; seed++) {
    u64 a = seed % Q, b = (seed * 7919) % Q, x = mulm(powm(G, a, P), powm(H, b, P), P);
    u64 A = a, B = b, X = x; unsigned long long it = 0;
    do { step(&x, &a, &b); step(&X, &A, &B); step(&X, &A, &B); it++; } while (x != X);
    /* g^a h^b = g^A h^B  ->  (B - b) log h = a - A  (mod q) */
    u64 db = (B + Q - b) % Q, da = (a + Q - A) % Q;
    if (db == 0) continue;
    u64 inv = powm(db, Q - 2, Q), sol = mulm(da, inv, Q);
    if (powm(G, sol, P) == H) { printf("%llu %llu\n", (unsigned long long)sol, it); return 0; }
  }
}
