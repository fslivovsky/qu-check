import QlrupChecker.Reader
import QlrupChecker.Qcir

open Qlrup

structure Opts where
  block : Nat := 4096
  stats : Bool := false
  chunk : Nat := 1048576
  readOnly : Bool := false
  files : List String := []

def parseArgs : List String → Opts → Option Opts
  | [], o => some { o with files := o.files.reverse }
  | "--stats" :: r, o => parseArgs r { o with stats := true }
  | "--block" :: n :: r, o => n.toNat?.bind fun n => parseArgs r { o with block := max n 1 }
  | "--read-only" :: r, o => parseArgs r { o with readOnly := true }
  | "--chunk" :: n :: r, o => n.toNat?.bind fun n => parseArgs r { o with chunk := n }
  | f :: r, o => if f.startsWith "--" then none else parseArgs r { o with files := f :: o.files }

@[noinline] def parseIO (text : String) : IO Qcir := pure (parseQcir text)
@[noinline] def mkEnvIO (q : Qcir) : IO Env := pure (mkEnv q)
@[noinline] def okIO (e : Env) : IO Bool := pure e.ok
@[noinline] def runBlockIO (e : Env) (st : State) (l : List Step) : IO Outcome :=
  pure (runBlock e st l)

def stepId : Step → String
  | .orig id .. | .derived id .. => s!"id {id}"
  | .delete _ => "deletion"

/-- Re-checks the proof step by step to locate the first rejected step. -/
partial def diagnose (e : Env) (path : String) (chunk blk : Nat) : IO String := do
  let r ← Reader.open path chunk
  let rec go (st : State) (n : Nat) : IO String := do
    match ← r.nextBlock blk with
    | .error m => return m
    | .ok none => return "unknown step"
    | .ok (some b) =>
      let rec steps (st : State) (i : Nat) (l : List Step) : Except String State :=
        match l with
        | [] => .ok st
        | s :: l =>
          match step e st s with
          | .more st => steps st (i + 1) l
          | .done _ => .error "done"
          | .fail => .error s!"step {i} ({stepId s}) rejected"
      match steps st n b.toList with
      | .ok st => go st (n + b.size)
      | .error m => return m
  go {} 1

partial def loop (e : Env) (r : Reader) (o : Opts) (st : State) (n : Nat)
    (nO nD nX : Nat) (tCheck : Nat) : IO UInt32 := do
  let report (nO nD nX tCheck : Nat) : IO Unit := do
    if o.stats then
      IO.eprintln s!"original {nO} derived {nD} deleted {nX}"
      IO.eprintln s!"time check {tCheck} ms"
  match ← r.nextBlock o.block with
  | .error m =>
    IO.println s!"s NOT VERIFIED: {m}"
    report nO nD nX tCheck
    return 1
  | .ok none =>
    IO.println "s NOT VERIFIED: proof ends without deriving the empty clause or term"
    report nO nD nX tCheck
    return 1
  | .ok (some b) =>
    let (a, d, x) := b.foldl (init := (0, 0, 0)) fun (a, d, x) s =>
      match s with
      | .orig .. => (a + 1, d, x)
      | .derived .. => (a, d + 1, x)
      | .delete _ => (a, d, x + 1)
    let nO := nO + a
    let nD := nD + d
    let nX := nX + x
    let t0 ← IO.monoMsNow
    let out ← if o.readOnly then pure (.more st) else runBlockIO e st b.toList
    let t1 ← IO.monoMsNow
    let tCheck := tCheck + (t1 - t0)
    match out with
    | .more st' => loop e r o st' (n + b.size) nO nD nX tCheck
    | .done res =>
      IO.println (if res then "s VERIFIED TRUE" else "s VERIFIED FALSE")
      report nO nD nX tCheck
      return 0
    | .fail =>
      let msg ← try diagnose e o.files[1]! o.chunk o.block catch _ => pure ""
      if msg.isEmpty then
        IO.println s!"s NOT VERIFIED: step rejected in block starting at step {n}"
      else
        IO.println s!"s NOT VERIFIED: {msg}"
      report nO nD nX tCheck
      return 1

def main (args : List String) : IO UInt32 := do
  let some o := parseArgs args {} | do
    IO.eprintln "usage: qlrup-check [--block N] [--stats] FORMULA.qcir PROOF"; return 2
  let [fq, fp] := o.files | do
    IO.eprintln "usage: qlrup-check [--block N] [--stats] FORMULA.qcir PROOF"; return 2
  let t0 ← IO.monoMsNow
  let text ← try IO.FS.readFile fq catch err =>
    IO.println s!"s NOT VERIFIED: cannot read formula: {err}"; return 1
  let q ← parseIO text
  let t1 ← IO.monoMsNow
  let e ← mkEnvIO q
  let ok ← okIO e
  let t2 ← IO.monoMsNow
  if o.stats then
    IO.eprintln s!"time parse formula {t1 - t0} ms, build env + well-formedness check {t2 - t1} ms"
  if !ok then
    IO.println "s NOT VERIFIED: malformed formula or prefix check failed"
    return 1
  let r ← try Reader.open fp o.chunk catch err =>
    IO.println s!"s NOT VERIFIED: cannot read proof: {err}"; return 1
  let t3 ← IO.monoMsNow
  let code ← loop e r o {} 1 0 0 0 0
  if o.stats then
    let t4 ← IO.monoMsNow
    IO.eprintln s!"time total proof (read+check) {t4 - t3} ms"
  return code
