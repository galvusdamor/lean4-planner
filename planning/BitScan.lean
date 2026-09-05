import Mathlib.Data.List.Range
import Mathlib.Tactic
import Strips.VarSet

/-!
# Enumerating the set bits of a bit vector

Every variable set of the STRIPS formalisation is a bit vector, and its list of members
(`STRIPS.VarSet.val`, used by `VarSet.toList`) is obtained by filtering the list of *all* `n`
variables.  That is the hottest primitive of the whole development: the `h^max` fixpoint
extracts the precondition and add lists of every action once per evaluation, the LM-cut
precondition-choice function walks the precondition list of every action once per round, the
successor generator reads add and delete lists, and so on.

Filtering `List.finRange n` costs `Θ(n)` list cells and `n` bit tests — and a bit test on a bit
vector is `Nat.testBit`, which *shifts the whole number*, so the enumeration costs `Θ(n²/64)`
machine words.

`bitScan` computes the same list one 64-bit word at a time: a word is extracted with a single
shift, is a machine integer, and is scanned by halving it until it is zero — so a word without
set bits costs a single test.  Measured with the `varsetprobe` harness the speed-up over the
filter is a factor of 8 at `n = 68`, 30 at `n = 200` and 46 at `n = 1000`.

The interface is `bitScan` together with `bitScan_eq`, which identifies it with the filter;
`planning.Planning` uses it to install a fast implementation of `STRIPS.VarSet.val` with
`@[csimp]`, so no statement about variable sets changes.
-/

namespace STRIPS

/-! ### The specification -/

/-- The ascending list of indices `j ∈ [i, i+len)` that are below `n` and at which the number
`x` has a set bit.  This is the specification of the scan. -/
def bitSeg (n x i len : ℕ) : List (Fin n) :=
  (List.range' i len).filterMap
    (fun j => if h : j < n then (if x.testBit j then some ⟨j, h⟩ else none) else none)

@[simp] lemma bitSeg_zero (n x i : ℕ) : bitSeg n x i 0 = [] := rfl

lemma bitSeg_succ (n x i len : ℕ) :
    bitSeg n x i (len + 1) =
      (if h : i < n then (if x.testBit i then [(⟨i, h⟩ : Fin n)] else []) else [])
        ++ bitSeg n x (i + 1) len := by
  unfold bitSeg
  rw [List.range'_succ, List.filterMap_cons]
  by_cases h : i < n
  · by_cases hb : x.testBit i <;> simp [h, hb]
  · simp [h]

lemma bitSeg_append (n x i a b : ℕ) :
    bitSeg n x i (a + b) = bitSeg n x i a ++ bitSeg n x (i + a) b := by
  unfold bitSeg
  rw [← List.range'_append_1, List.filterMap_append]

/-- If `x` has no set bit in `[i, i+len)`, the segment is empty. -/
lemma bitSeg_eq_nil (n x i len : ℕ) (h : ∀ j, i ≤ j → j < i + len → x.testBit j = false) :
    bitSeg n x i len = [] := by
  unfold bitSeg
  apply List.filterMap_eq_nil_iff.mpr
  intro j hj
  rw [List.mem_range'_1] at hj
  by_cases hn : j < n
  · simp [hn, h j hj.1 hj.2]
  · simp [hn]

/-! ### Bit arithmetic of one machine word -/

/-- The window `[i, i+len)` of `x`, as a number. -/
private abbrev win (x i len : ℕ) : ℕ := (x >>> i) % 2 ^ len

private lemma win_testBit_zero (x i len : ℕ) :
    (win x i (len + 1)).testBit 0 = x.testBit i := by
  rw [win, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp

private lemma win_shiftRight (x i len : ℕ) :
    (win x i (len + 1)) >>> 1 = win x (i + 1) len := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_shiftRight, win, win, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hk : k < len
  · simp only [hk, decide_true, Bool.true_and, show 1 + k < len + 1 by omega, decide_true]
    congr 1
    omega
  · simp only [hk, decide_false, Bool.false_and, show ¬ (1 + k < len + 1) by omega, decide_false,
      Bool.false_and]

private lemma testBit_of_win_eq_zero {x i len : ℕ} (h : win x i len = 0) {j : ℕ}
    (hij : i ≤ j) (hj : j < i + len) : x.testBit j = false := by
  have hb : (win x i len).testBit (j - i) = false := by rw [h]; simp
  rw [win, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight] at hb
  have hlt : j - i < len := by omega
  simp only [hlt, decide_true, Bool.true_and] at hb
  rwa [show i + (j - i) = j by omega] at hb

/-! ### The scan -/

/-- One word of the scan: the set bits of the machine word `w`, whose bit `0` is bit `i` of the
number being scanned, in *descending* order, prepended to `acc`.  The loop stops as soon as the
remaining word is zero, so a zero word costs a single test. -/
def scanWord (n : ℕ) : (fuel i w : ℕ) → List (Fin n) → List (Fin n)
  | 0, _, _, acc => acc
  | fuel + 1, i, w, acc =>
      if w = 0 then acc
      else
        scanWord n fuel (i + 1) (w >>> 1)
          (if w.testBit 0 then (if h : i < n then (⟨i, h⟩ : Fin n) :: acc else acc) else acc)

/-- The scan of a word lists exactly the bits of `x` in the window it stands for. -/
lemma scanWord_eq (n : ℕ) :
    ∀ (fuel x i : ℕ) (acc : List (Fin n)),
      scanWord n fuel i (win x i fuel) acc = (bitSeg n x i fuel).reverse ++ acc := by
  intro fuel
  induction fuel with
  | zero => intro x i acc; simp [scanWord]
  | succ fuel ih =>
      intro x i acc
      rw [scanWord]
      by_cases hz : win x i (fuel + 1) = 0
      · rw [if_pos hz, bitSeg_eq_nil n x i (fuel + 1) (fun j h1 h2 =>
          testBit_of_win_eq_zero hz h1 h2)]
        simp
      · rw [if_neg hz, win_shiftRight, win_testBit_zero, ih, bitSeg_succ]
        by_cases h : i < n
        · by_cases hb : x.testBit i <;> simp [h, hb]
        · simp [h]

/-- The whole scan: the words `0, …, k-1` of `x`, in descending order, prepended to `acc`. -/
def scanWords (n x : ℕ) : (k : ℕ) → List (Fin n) → List (Fin n)
  | 0, acc => acc
  | k + 1, acc =>
      scanWord n 64 (64 * k) ((x >>> (64 * k)) % 18446744073709551616) (scanWords n x k acc)

lemma scanWords_eq (n x : ℕ) :
    ∀ (k : ℕ) (acc : List (Fin n)),
      scanWords n x k acc = (bitSeg n x 0 (64 * k)).reverse ++ acc := by
  intro k
  induction k with
  | zero => intro acc; simp [scanWords]
  | succ k ih =>
      intro acc
      have hpow : (18446744073709551616 : ℕ) = 2 ^ 64 := by norm_num
      rw [scanWords, ih, hpow, show (x >>> (64 * k)) % 2 ^ 64 = win x (64 * k) 64 from rfl,
        scanWord_eq]
      rw [show 64 * (k + 1) = 64 * k + 64 by ring, bitSeg_append, List.reverse_append,
        List.append_assoc]
      simp

/-- **The set bits of a bit vector, scanned one machine word at a time.** -/
def bitScan {n : ℕ} (b : BitVec n) : List (Fin n) :=
  (scanWords n b.toNat ((n + 63) / 64) []).reverse

/-! ### The scan is the filter -/

private lemma bitSeg_map_val (n x i len : ℕ) :
    (bitSeg n x i len).map Fin.val
      = (List.range' i len).filter (fun j => decide (j < n) && x.testBit j) := by
  induction len generalizing i with
  | zero => simp [bitSeg]
  | succ len ih =>
      rw [bitSeg_succ, List.map_append, ih, List.range'_succ, List.filter_cons]
      by_cases h : i < n
      · by_cases hb : x.testBit i <;> simp [h, hb]
      · simp [h]

private lemma filter_range'_eq (n x m : ℕ) (hm : n ≤ m) :
    (List.range' 0 m).filter (fun j => decide (j < n) && x.testBit j)
      = (List.range n).filter (fun j => x.testBit j) := by
  rw [show m = n + (m - n) by omega, ← List.range'_append_1, List.filter_append,
    List.range_eq_range']
  have h1 : (List.range' 0 n).filter (fun j => decide (j < n) && x.testBit j)
      = (List.range' 0 n).filter (fun j => x.testBit j) := by
    apply List.filter_congr
    intro j hj
    rw [List.mem_range'_1] at hj
    simp [show j < n by omega]
  have h2 : (List.range' (0 + n) (m - n)).filter (fun j => decide (j < n) && x.testBit j) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj
    rw [List.mem_range'_1] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro hlt
    omega
  rw [h1, h2, List.append_nil]

/-- **The scan is the filter of the list of all variables.** -/
theorem bitScan_eq {n : ℕ} (b : BitVec n) :
    bitScan b = (List.finRange n).filter (fun i => b.toNat.testBit i.val) := by
  have hmap : (bitScan b).map Fin.val
      = ((List.finRange n).filter (fun i => b.toNat.testBit i.val)).map Fin.val := by
    rw [bitScan, scanWords_eq]
    simp only [List.append_nil, List.reverse_reverse]
    rw [bitSeg_map_val, filter_range'_eq n b.toNat _ (by omega)]
    rw [show ((List.finRange n).filter (fun i => b.toNat.testBit i.val)).map Fin.val
        = ((List.finRange n).map Fin.val).filter (fun j => b.toNat.testBit j) from
      (List.filter_map (l := List.finRange n) (f := Fin.val)
        (p := fun j => b.toNat.testBit j)).symm]
    rw [List.map_coe_finRange_eq_range]
  exact List.map_injective_iff.mpr Fin.val_injective hmap

end STRIPS
