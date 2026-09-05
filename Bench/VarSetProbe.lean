import planning.Planning

/-!
Scratch benchmark (development aid, not part of the library): how expensive is
`VarSet.val` and what do alternative implementations cost?

Run with `lake env lean --run scratch/VarSetProbe.lean`.
-/

open STRIPS

/-- Current implementation: filter the list of all variables. -/
def valA {n : ℕ} (V : VarSet n) : List (Fin n) := (List.finRange n).filter (fun i => i ∈ V)

/-- Descending recursion over the bit indices, no intermediate list. -/
def valDown {n : ℕ} (V : VarSet n) : (k : ℕ) → k ≤ n → List (Fin n) → List (Fin n)
  | 0, _, acc => acc
  | k + 1, h, acc =>
      valDown V k (by omega)
        (if V.toBitVec[k]'(by omega) then (⟨k, by omega⟩ : Fin n) :: acc else acc)

def valB {n : ℕ} (V : VarSet n) : List (Fin n) := valDown V n (le_refl n) []

/-- Word-wise: 64 bits at a time, skipping words that are zero. -/
def valWord {n : ℕ} (V : VarSet n) (w : ℕ) : (k : ℕ) → k ≤ 64 → List (Fin n) → List (Fin n)
  | 0, _, acc => acc
  | k + 1, h, acc =>
      let i := 64 * w + k
      if hi : i < n then
        valWord V w k (by omega) (if V.toBitVec[i] then (⟨i, hi⟩ : Fin n) :: acc else acc)
      else valWord V w k (by omega) acc

def valWords {n : ℕ} (V : VarSet n) : ℕ → List (Fin n) → List (Fin n)
  | 0, acc => acc
  | w + 1, acc =>
      let word := (V.toBitVec.toNat >>> (64 * w)) % 18446744073709551616
      valWords V w (if word == 0 then acc else valWord V w 64 (le_refl 64) acc)

def valC {n : ℕ} (V : VarSet n) : List (Fin n) := valWords V ((n + 63) / 64) []

/-- Word-wise with a scalar inner loop that stops at the highest set bit of the word. -/
def valWordD {n : ℕ} (base : ℕ) : (fuel : ℕ) → (j : ℕ) → (w : ℕ) → List (Fin n) → List (Fin n)
  | 0, _, _, acc => acc
  | fuel + 1, j, w, acc =>
      if w == 0 then acc
      else
        let acc := if w % 2 == 1 then
            (if h : base + j < n then (⟨base + j, h⟩ : Fin n) :: acc else acc)
          else acc
        valWordD base fuel (j + 1) (w >>> 1) acc

def valWordsD {n : ℕ} (x : ℕ) (nw : ℕ) : ℕ → List (Fin n) → List (Fin n)
  | 0, acc => acc
  | k + 1, acc =>
      let w := nw - (k + 1)
      valWordsD x nw k (valWordD (64 * w) 64 0 ((x >>> (64 * w)) % 18446744073709551616) acc)

def valD {n : ℕ} (V : VarSet n) : List (Fin n) :=
  let nw := (n + 63) / 64
  (valWordsD V.toBitVec.toNat nw nw []).reverse

def valWordsE {n : ℕ} (x : ℕ) (nw : ℕ) : ℕ → List (Fin n) → List (Fin n)
  | 0, acc => acc
  | k + 1, acc =>
      let w := nw - (k + 1)
      valWordsE x nw k (valWordD (32 * w) 32 0 ((x >>> (32 * w)) % 4294967296) acc)

def valE {n : ℕ} (V : VarSet n) : List (Fin n) :=
  let nw := (n + 31) / 32
  (valWordsE V.toBitVec.toNat nw nw []).reverse

/-- Two-level scan: 64-bit words, each scanned byte by byte. -/
def valBytes {n : ℕ} (w : ℕ) (base : ℕ) : ℕ → List (Fin n) → List (Fin n)
  | 0, acc => acc
  | k + 1, acc =>
      valWordD (base + 8 * k) 8 0 ((w >>> (8 * k)) % 256) (valBytes w base k acc)

def valWordsF {n : ℕ} (x : ℕ) (nw : ℕ) : ℕ → List (Fin n) → List (Fin n)
  | 0, acc => acc
  | k + 1, acc =>
      let w := nw - (k + 1)
      valWordsF x nw k (valBytes ((x >>> (64 * w)) % 18446744073709551616) (64 * w) 8 acc)

def valF {n : ℕ} (V : VarSet n) : List (Fin n) :=
  let nw := (n + 63) / 64
  (valWordsF V.toBitVec.toNat nw nw []).reverse

def timeRep (name : String) (reps : ℕ) (f : Unit → ℕ) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for _ in [0:reps] do
    acc := acc + f ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {acc} ({(t1 - t0) / (max reps 1)} ns/call)"

/-- `m` sets over `n` variables, each holding the bits `i` with `i % step == r`. -/
def mkSets (n : ℕ) (m : ℕ) (step : ℕ) : List (VarSet n) :=
  (List.range m).map (fun r =>
    VarSet.ofList ((List.finRange n).filter (fun i => i.val % step == r % step)))

def bench (n : ℕ) (m : ℕ) (step : ℕ) : IO Unit := do
  let sets := mkSets n m step
  IO.println s!"--- n = {n}, {m} sets, every {step}-th bit set"
  timeRep "  valA (current)" 200 (fun _ => (sets.map (fun V => (valA V).length)).sum)
  timeRep "  valB (bitwise)" 200 (fun _ => (sets.map (fun V => (valB V).length)).sum)
  timeRep "  valC (wordwise)" 200 (fun _ => (sets.map (fun V => (valC V).length)).sum)
  timeRep "  valD (scalar)  " 200 (fun _ => (sets.map (fun V => (valD V).length)).sum)
  timeRep "  valE (32-bit)  " 200 (fun _ => (sets.map (fun V => (valE V).length)).sum)
  timeRep "  valF (2-level) " 200 (fun _ => (sets.map (fun V => (valF V).length)).sum)

def main : IO Unit := do
  -- sanity: the three agree
  let sets := mkSets 100 7 5
  IO.println s!"agree: {sets.all (fun V => valA V == valB V && valA V == valC V && valA V == valD V && valA V == valE V && valA V == valF V)}"
  bench 12 40 4
  bench 24 40 6
  bench 40 40 10
  bench 68 52 20
  bench 200 200 40
  bench 338 384 100
  bench 1000 500 200


