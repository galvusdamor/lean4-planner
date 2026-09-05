import Mathlib.Tactic
/-!
Scratch benchmark (development aid): is a `let` in a definition body shared at run time, or is
it zeta-expanded so that its value is recomputed at every occurrence?  The answer decides how
the LM-cut round has to be written (see `planning/LMCutRun.lean`).
-/

/-- Something expensive to compute. -/
def expensive (k : ℕ) : List ℕ := (List.range k).map (fun i => i * i % 7)

/-- Two occurrences of a plain `let`. -/
def withLet (k : ℕ) : ℕ :=
  let a := expensive k
  a.length + a.sum

/-- Two occurrences of an argument. -/
def withArgOf (a : List ℕ) : ℕ := a.length + a.sum

def withArg (k : ℕ) : ℕ := withArgOf (expensive k)

/-- Two occurrences, one of them inside a proof-carrying `dite` (the shape of `lmcut_step`). -/
def withLetProof (k : ℕ) : ℕ :=
  let a := expensive k
  let m := if h : a = [] then 0 else (a.map (fun x => x + 1)).length
  a.length + m

/-- The same, with the value passed as an argument. -/
def withArgProofOf (a : List ℕ) : ℕ :=
  let m := if h : a = [] then 0 else (a.map (fun x => x + 1)).length
  a.length + m

def withArgProof (k : ℕ) : ℕ := withArgProofOf (expensive k)

def timeRep (name : String) (reps : ℕ) (f : Unit → ℕ) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for _ in [0:reps] do
    acc := acc + f ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {acc} ({(t1 - t0) / (max reps 1)} ns/call)"

def main : IO Unit := do
  let k := 20000
  timeRep "  expensive once" 100 (fun _ => (expensive k).length)
  timeRep "  withLet       " 100 (fun _ => withLet k)
  timeRep "  withArg       " 100 (fun _ => withArg k)
  timeRep "  withLetProof  " 100 (fun _ => withLetProof k)
  timeRep "  withArgProof  " 100 (fun _ => withArgProof k)
