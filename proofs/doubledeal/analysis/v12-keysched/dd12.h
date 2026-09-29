#pragma once
/* DoubleDeal v12 in C (scratch, analysis only). Reuses the v11 round layers from
   ../passkey-related-key/dd.h (v12 round function = v11) and adds the v12 PassKey (SPEC 3.7).
   Cross-checked against security/checks/ddport.py (v=12) and the committed vectors by xcheck12.py. */
#include "../passkey-related-key/dd.h"
static inline void deal_under_(int *xs, int n, int d) { int t[52];
    for (int i = 0; i < n - d; i++) t[i] = xs[d + i];
    for (int i = 0; i < d; i++) t[n - d + i] = xs[d - 1 - i];
    memcpy(xs, t, n * sizeof(int)); }
static inline void passkey12(const int *deck, int *o) { int hand[52], key[52], hn = 52, kn = 0;
    memcpy(hand, deck, 52 * sizeof(int));
    for (int s = 0; s < 52; s++) {
        int C = hand[0]; memmove(hand, hand + 1, (hn - 1) * sizeof(int)); hn--;
        int d = SUIT(C) + 2;
        if (d < hn) deal_under_(hand, hn, d); else if (d < kn) deal_under_(key, kn, d);
        int r = RANK(C);
        if (hn && r < hn) rotl(hand, hn, r); else if (kn && r < kn) rotl(key, kn, r);
        memmove(key + 1, key, kn * sizeof(int)); key[0] = C; kn++; }
    memcpy(o, key, 52 * sizeof(int)); }
static inline void unkeyed(const int *x, int *o) { int t[52]; stem(x, t); mix_v11(t, o); }
static inline void rel(const int *s, const int *x, int *o) { for (int i = 0; i < 52; i++) o[i] = s[x[i]]; }
/* RoundChar (TrailBound.lean): SumRanks commutes with s at lay(x), and GridCycle commutes with s at
   stem(x). Tested as stem(s.x) == s.stem(x): ShiftRows and the scoop only move seats (they commute with
   any relabelling) and are injective, so this is the same event as SumRanks commuting. */
static inline int roundchar(const int *s, const int *x) { int sx[52], a[52], b[52], sa[52], ma[52], mb[52], sma[52];
    rel(s, x, sx); stem(x, a); stem(sx, b); rel(s, a, sa); if (!same(b, sa)) return 0;
    mix_v11(a, ma); mix_v11(b, mb); rel(s, ma, sma); return same(mb, sma); }
