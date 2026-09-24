/-
  Concrete TwoDeck: real PassKey key schedule wired as Compose `pos` maps,
  plus list-level encrypt/decrypt matching twodeck.sudo. The abstract
  round-trip theorems in Round.lean apply once the master key is a
  permutation of 0..51 (Perm52). Correctness, not bit-security.
-/
import TwoDeck.Basic
import TwoDeck.Compose
import TwoDeck.PassKey
import TwoDeck.Grid
import TwoDeck.SumRanks
import TwoDeck.ShiftRows
import TwoDeck.GridCycle
import TwoDeck.Round
import TwoDeck.Factoradic

namespace TwoDeck

/-! ## Packet lists -/

def toDeck (f : Fin 52 → Nat) : List Nat := (Array.ofFn f).toList

theorem length_toDeck (f : Fin 52 → Nat) : (toDeck f).length = 52 := by
  simp [toDeck, Array.size_ofFn]

def ofDeck (d : List Nat) (h : d.length = 52) : Fin 52 → Nat :=
  fun i => d[i.val]'(by omega)

/-- Apply a packet map when `d` is length 52; otherwise return `d`. -/
def onDeck (f : (Fin 52 → Nat) → (Fin 52 → Nat)) (d : List Nat) : List Nat :=
  if h : d.length = 52 then toDeck (f (ofDeck d h)) else d

/-! ## Index-of (first occurrence) -/

def indexOf : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, c => if x = c then 0 else indexOf xs c + 1

theorem indexOf_lt_of_mem :
    ∀ (l : List Nat) (c : Nat), c ∈ l → indexOf l c < l.length
  | [], c, h => by cases h
  | x :: xs, c, h => by
      simp only [indexOf, List.length_cons]
      split
      · omega
      · next hne =>
        have hm : c ∈ xs := by
          cases List.mem_cons.mp h with
          | inl heq => exact absurd heq.symm hne
          | inr hm => exact hm
        have ih := indexOf_lt_of_mem xs c hm
        omega

theorem get_indexOf :
    ∀ (l : List Nat) (c : Nat) (h : c ∈ l),
      l[indexOf l c]'(indexOf_lt_of_mem l c h) = c
  | x :: xs, c, h => by
      simp only [indexOf]
      split
      · next heq =>
        simp [heq]
      · next hne =>
        have hm : c ∈ xs := by
          cases List.mem_cons.mp h with
          | inl heq => exact absurd heq.symm hne
          | inr hm => exact hm
        have hlt := indexOf_lt_of_mem xs c hm
        have hcons : indexOf xs c + 1 < (x :: xs).length := by simp; omega
        have : (x :: xs)[indexOf xs c + 1]'hcons = xs[indexOf xs c]'hlt :=
          List.getElem_cons_succ x xs (indexOf xs c) hcons
        rw [this]
        exact get_indexOf xs c hm

theorem indexOf_eq_of_get :
    ∀ (l : List Nat) (i : Nat) (hi : i < l.length) (hn : l.Nodup),
      indexOf l (l[i]'hi) = i
  | x :: xs, 0, _hi, _hn => by
      simp [indexOf]
  | x :: xs, i + 1, hi, hn => by
      have hi' : i < xs.length := by simp at hi; omega
      have ⟨hnotin, hn'⟩ := List.nodup_cons.mp hn
      have hmem : xs[i]'hi' ∈ xs := List.getElem_mem hi'
      have hne : x ≠ xs[i]'hi' := fun he => hnotin (he ▸ hmem)
      have hget : (x :: xs)[i + 1]'hi = xs[i]'hi' :=
        List.getElem_cons_succ x xs i hi
      simp only [indexOf, hget, hne, ite_false]
      have ih := indexOf_eq_of_get xs i hi' hn'
      rw [ih]

/-! ## Key decks as Compose bijections -/

/-- A 52-card key: a permutation of `{0,…,51}`. -/
structure Perm52 (key : List Nat) : Prop where
  length : key.length = 52
  nodup : key.Nodup
  bounded : ∀ x ∈ key, x < 52
  complete : ∀ j : Fin 52, j.val ∈ key

theorem Perm52.of_perm {k k' : List Nat} (h : Perm52 k) (hp : List.Perm k' k) :
    Perm52 k' where
  length := hp.length_eq.trans h.length
  nodup := hp.symm.nodup h.nodup
  bounded := fun x hx => h.bounded x (hp.mem_iff.mp hx)
  complete := fun j => hp.mem_iff.mpr (h.complete j)

def clampFin (n : Nat) : Fin 52 :=
  if h : n < 52 then ⟨n, h⟩ else ⟨0, by decide⟩

theorem clampFin_of_lt (n : Nat) (h : n < 52) : clampFin n = ⟨n, h⟩ := by
  simp [clampFin, h]

/-- Seat of card `j` in the key deck (`index_of` in twodeck.sudo). -/
def keyPos (key : List Nat) (j : Fin 52) : Fin 52 :=
  clampFin (indexOf key j.val)

/-- Card at seat `i` (`k[i]`). -/
def keyInvPos (key : List Nat) (i : Fin 52) : Fin 52 :=
  if h : i.val < key.length then clampFin (key[i.val]'h) else ⟨0, by decide⟩

theorem keyInvPos_keyPos (key : List Nat) (hk : Perm52 key) (j : Fin 52) :
    keyInvPos key (keyPos key j) = j := by
  have hlen := hk.length
  have hj := hk.complete j
  have hlt := indexOf_lt_of_mem key j.val hj
  have hidx52 : indexOf key j.val < 52 := by omega
  have hpos : keyPos key j = ⟨indexOf key j.val, hidx52⟩ := by
    simp [keyPos, clampFin_of_lt (indexOf key j.val) hidx52]
  have hidx : (keyPos key j).val < key.length := by
    simp [hpos]; omega
  have hget := get_indexOf key j.val hj
  simp only [keyInvPos, hidx, ↓reduceDIte]
  have : key[(keyPos key j).val]'hidx = j.val := by
    simp [hpos, hget]
  rw [this, clampFin_of_lt j.val j.isLt]

theorem keyPos_keyInvPos (key : List Nat) (hk : Perm52 key) (i : Fin 52) :
    keyPos key (keyInvPos key i) = i := by
  have hlen := hk.length
  have hi : i.val < key.length := by omega
  have hmem : key[i.val]'hi ∈ key := List.getElem_mem hi
  have hcard : key[i.val]'hi < 52 := hk.bounded _ hmem
  have hinv : keyInvPos key i = ⟨key[i.val]'hi, hcard⟩ := by
    simp [keyInvPos, hi, clampFin_of_lt (key[i.val]'hi) hcard]
  have hidx := indexOf_eq_of_get key i.val hi hk.nodup
  simp only [keyPos, hinv]
  have : indexOf key (key[i.val]'hi) = i.val := hidx
  rw [this, clampFin_of_lt i.val i.isLt]

/-! ## PassKey iterates (K0..K6) -/

def passKeyIter : Nat → List Nat → List Nat
  | 0, k => k
  | n + 1, k => passToKeyCutFallback (passKeyIter n k)

theorem passKeyIter_perm52 (k : List Nat) (hk : Perm52 k) :
    ∀ n, Perm52 (passKeyIter n k)
  | 0 => hk
  | n + 1 =>
      Perm52.of_perm (passKeyIter_perm52 k hk n)
        (passToKeyCutFallback_perm (passKeyIter n k))

def expandKeys (k0 : List Nat) : List (List Nat) :=
  [0, 1, 2, 3, 4, 5, 6].map (fun r => passKeyIter r k0)

/-! ## Concrete encrypt / decrypt (PassKey schedule) -/

/-- Whitening K0, five mix rounds K1..K5, final no-mix K6. -/
def encryptDeckFn (m : Fin 52 → Nat) (key : List Nat) : Fin 52 → Nat :=
  encrypt6 m (keyPos key)
    (fun r => keyPos (passKeyIter (r + 1) key))
    (keyPos (passKeyIter 6 key))

def decryptDeckFn (c : Fin 52 → Nat) (key : List Nat) : Fin 52 → Nat :=
  decrypt6 c
    (keyPos key) (keyInvPos key)
    (fun r => keyPos (passKeyIter (r + 1) key))
    (fun r => keyInvPos (passKeyIter (r + 1) key))
    (keyPos (passKeyIter 6 key))
    (keyInvPos (passKeyIter 6 key))

/-- S2 for the real schedule: abstract `encrypt6_rt` instantiated at PassKey `pos`. -/
theorem encryptDeckFn_rt (m : Fin 52 → Nat) (key : List Nat) (hk : Perm52 key) :
    decryptDeckFn (encryptDeckFn m key) key = m :=
  encrypt6_rt m
    (keyPos key) (keyInvPos key)
    (fun r => keyPos (passKeyIter (r + 1) key))
    (fun r => keyInvPos (passKeyIter (r + 1) key))
    (keyPos (passKeyIter 6 key))
    (keyInvPos (passKeyIter 6 key))
    (fun j => keyInvPos_keyPos key hk j)
    (fun i => keyPos_keyInvPos key hk i)
    (fun r j => keyInvPos_keyPos (passKeyIter (r + 1) key)
      (passKeyIter_perm52 key hk (r + 1)) j)
    (fun r i => keyPos_keyInvPos (passKeyIter (r + 1) key)
      (passKeyIter_perm52 key hk (r + 1)) i)
    (fun j => keyInvPos_keyPos (passKeyIter 6 key) (passKeyIter_perm52 key hk 6) j)
    (fun i => keyPos_keyInvPos (passKeyIter 6 key) (passKeyIter_perm52 key hk 6) i)

theorem perm52_range : Perm52 (List.range 52) where
  length := List.length_range 52
  nodup := List.nodup_range 52
  bounded := fun _ hx => List.mem_range.mp hx
  complete := fun j => List.mem_range.mpr j.isLt

theorem encryptDeckFn_rt_range (m : Fin 52 → Nat) :
    decryptDeckFn (encryptDeckFn m (List.range 52)) (List.range 52) = m :=
  encryptDeckFn_rt m (List.range 52) perm52_range

def encryptDeck (message key : List Nat) : List Nat :=
  if h : message.length = 52 then toDeck (encryptDeckFn (ofDeck message h) key)
  else message

def decryptDeck (cipher key : List Nat) : List Nat :=
  if h : cipher.length = 52 then toDeck (decryptDeckFn (ofDeck cipher h) key)
  else cipher

/-! ## Layer packets used by known-answer vectors -/

def mixColumnsDeck (d : List Nat) : List Nat := onDeck mixColumns d

def sumRanksDeck (d : List Nat) : List Nat :=
  if h : d.length = 52 then
    toDeck (scoopColumnMajor (sumRanks cardRank (layColumnMajor (ofDeck d h))))
  else d

def shiftRowsDeck (d : List Nat) : List Nat :=
  if h : d.length = 52 then
    toDeck (scoopColumnMajor (shiftRows (layColumnMajor (ofDeck d h))))
  else d

def unkeyedFullDeck (d : List Nat) : List Nat := onDeck unkeyedWithMix d

def composeDeck (m k : List Nat) : List Nat :=
  if h : m.length = 52 then
    toDeck (composeVec 52 Nat (ofDeck m h) (keyPos k))
  else m

def ctrEncryptBlocks (blocks : List (List Nat)) (key nonce : List Nat) :
    List (List Nat) :=
  go 0 blocks
where
  go : Nat → List (List Nat) → List (List Nat)
    | _, [] => []
    | i, b :: rest =>
        composeDeck b (encryptDeck (counterDeck nonce i) key) :: go (i + 1) rest

end TwoDeck
