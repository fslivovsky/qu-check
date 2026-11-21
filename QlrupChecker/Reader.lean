import QlrupChecker.Run

/-!
# Streaming reader for QLRUP proofs (unverified)

Reads text or binary proofs (see `doc/proof-format.md`) in large chunks and produces
`Qlrup.Step`s.  Nothing here is trusted: the verified checker only sees the resulting steps.
-/

namespace Qlrup

/-- Reader state: a buffer window of the file. -/
structure RS where
  h : IO.FS.Handle
  chunk : Nat
  binary : Bool
  buf : ByteArray := ByteArray.empty
  pos : Nat := 0
  eof : Bool := false
  /-- Number of file bytes before `buf[0]`. -/
  base : Nat := 0
  /-- Current line (text format). -/
  line : Nat := 1
  /-- An empty constraint has been returned. -/
  done : Bool := false

/-- A streaming proof reader. -/
structure Reader where
  st : IO.Ref RS
  binary : Bool

private inductive ScanR where
  | done
  | more
  | err (msg : String)
  deriving Inhabited

private inductive Tok where
  | num (neg : Bool) (n : Nat)
  | word (c : UInt8)
  | eol
  | eof
  | more
  | err (msg : String)

private def RS.errMsg (s : RS) (msg : String) : String :=
  if s.binary then s!"byte offset {s.base + s.pos}: {msg}" else s!"line {s.line}: {msg}"

private def RS.fail {α} (s : RS) (msg : String) : IO α := throw (IO.userError (s.errMsg msg))

/-- Reads the next chunk, keeping the unconsumed part of the buffer. -/
private def RS.refill (s : RS) : IO RS := do
  if s.eof then return s
  let c ← s.h.read s.chunk.toUSize
  if c.size == 0 then return { s with eof := true }
  let rest := if s.pos < s.buf.size then s.buf.extract s.pos s.buf.size ++ c else c
  return { s with buf := rest, base := s.base + s.pos, pos := 0 }

/-! ### Pure scanners -/

@[inline] private def isWs (c : UInt8) : Bool := c == 32 || c == 9 || c == 13
@[inline] private def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

private partial def skipWs (buf : ByteArray) (i : Nat) : Nat :=
  if h : i < buf.size then (if isWs buf[i] then skipWs buf (i + 1) else i) else i

private partial def skipLine (buf : ByteArray) (i : Nat) : Option Nat :=
  if h : i < buf.size then (if buf[i] == 10 then some (i + 1) else skipLine buf (i + 1)) else none

private partial def tokEnd (buf : ByteArray) (i : Nat) : Nat :=
  if h : i < buf.size then
    (let c := buf[i]; if isWs c || c == 10 then i else tokEnd buf (i + 1))
  else i

/-- Scans one text token.  Returns the token and the new position. -/
private def scanTextTok (buf : ByteArray) (pos : Nat) (eof first : Bool) : Tok × Nat :=
  let i := skipWs buf pos
  if h : i < buf.size then
    let c := buf[i]
    if c == 10 then (.eol, i + 1)
    else if first && c == 35 then
      match skipLine buf i with
      | some j => (.eol, j)
      | none => if eof then (.eol, buf.size) else (.more, pos)
    else
      let e := tokEnd buf i
      if e == buf.size && !eof then (.more, pos)
      else
        let neg := c == 45
        let s := if neg then i + 1 else i
        if s < e && isDigit buf[s]! then
          let rec go (k v : Nat) : Option Nat :=
            if k < e then (let d := buf[k]!; if isDigit d then go (k + 1) (v * 10 + (d - 48).toNat) else none)
            else some v
          termination_by e - k
          decreasing_by all_goals omega
          match go s 0 with
          | some v => (.num neg v, e)
          | none => (.err "bad token", e)
        else if e == i + 1 && ((65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)) then (.word c, e)
        else (.err "bad token", e)
  else if eof then (.eof, buf.size) else (.more, pos)

/-- Scans a varint at `i`. -/
private partial def scanVar (buf : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  let rec go (j x shift : Nat) : Option (Nat × Nat) :=
    if h : j < buf.size then
      let b := buf[j]
      let x := x ||| ((b.toNat &&& 0x7f) <<< shift)
      if b &&& 0x80 != 0 then go (j + 1) x (shift + 7) else some (x, j + 1)
    else none
  go i 0 0

/-- Scans a `0`-terminated list in the text format. -/
@[specialize] private partial def scanListText {α} (mk : Nat → Bool → α) (allowNeg : Bool)
    (buf : ByteArray) (pos : Nat) (eof : Bool) (acc : Array α) : ScanR × Nat × Array α :=
  let n := buf.size
  let rec go (i : Nat) (acc : Array α) : ScanR × Nat × Array α :=
    let i := skipWs buf i
    if h : i < n then
      if buf[i] == 10 then (.err "missing terminating 0", i, acc)
      else
        let neg := buf[i] == 45
        let s := if neg then i + 1 else i
        let rec digits (k v : Nat) : Nat × Nat :=
          if h : k < n then
            (let d := buf[k]; if isDigit d then digits (k + 1) (v * 10 + (d - 48).toNat) else (k, v))
          else (k, v)
        let (k, v) := digits s 0
        if k ≥ n && !eof then (.more, i, acc)
        else if k == s then (.err "bad token", i, acc)
        else if k < n && !(isWs buf[k]! || buf[k]! == 10) then (.err "bad token", i, acc)
        else if v == 0 then (.done, k, acc)
        else if neg && !allowNeg then (.err "negative identifier", i, acc)
        else go k (acc.push (mk v neg))
    else if eof then (.err "missing terminating 0", i, acc) else (.more, i, acc)
  go pos acc

/-- Scans a `0`-terminated list in the binary format. -/
@[specialize] private partial def scanListBin {α} (mk : Nat → Bool → α) (lit : Bool)
    (buf : ByteArray) (pos : Nat) (eof : Bool) (acc : Array α) : ScanR × Nat × Array α :=
  let rec go (i : Nat) (acc : Array α) : ScanR × Nat × Array α :=
    let r : Option (Nat × Nat) :=
      if h : i < buf.size then
        (let b := buf[i]; if b < 128 then some (b.toNat, i + 1) else scanVar buf i)
      else none
    match r with
    | none => if eof then (.err "unexpected end of file", i, acc) else (.more, i, acc)
    | some (x, j) =>
      if x == 0 then (.done, j, acc)
      else if lit then
        if x == 1 then (.err "literal encoding 1 denotes variable 0", i, acc)
        else go j (acc.push (mk (x >>> 1) (x % 2 == 1)))
      else go j (acc.push (mk x false))
  go pos acc

/-! ### Reading with refills -/

private def litMk (v : Nat) (neg : Bool) : Lit := (v, !neg)
private def idMk (v : Nat) (_ : Bool) : Nat := v

private partial def readList {α} (s : RS) (mk : Nat → Bool → α) (lit : Bool) (acc : Array α) :
    IO (RS × Array α) := do
  let (r, p, acc) :=
    if s.binary then scanListBin mk lit s.buf s.pos s.eof acc
    else scanListText mk lit s.buf s.pos s.eof acc
  let s := { s with pos := p }
  match r with
  | .done => return (s, acc)
  | .more => readList (← s.refill) mk lit acc
  | .err m => s.fail m

private def readLits (s : RS) : IO (RS × List Lit) := do
  let (s, a) ← readList s litMk true #[]
  return (s, a.toList)

private def readIds (s : RS) : IO (RS × List Nat) := do
  let (s, a) ← readList s idMk false #[]
  return (s, a.toList)

private partial def textTok (s : RS) (first : Bool) : IO (RS × Tok) := do
  let (t, p) := scanTextTok s.buf s.pos s.eof first
  match t with
  | .more => textTok (← s.refill) first
  | .err m => s.fail m
  | .eol => return ({ s with pos := p, line := s.line + 1 }, t)
  | t => return ({ s with pos := p }, t)

private def textNat (s : RS) (what : String) : IO (RS × Nat) := do
  let (s, t) ← textTok s false
  match t with
  | .num false n => return (s, n)
  | .num true _ => s.fail s!"negative {what}"
  | _ => s.fail s!"missing {what}"

private def textType (s : RS) : IO (RS × Bool) := do
  let (s, t) ← textTok s false
  match t with
  | .word 99 => return (s, false)
  | .word 116 => return (s, true)
  | _ => s.fail "bad constraint type"

private def textEnd (s : RS) : IO RS := do
  let (s, t) ← textTok s false
  match t with
  | .eol | .eof => return s
  | _ => s.fail "trailing tokens after final 0"

private partial def binNat (s : RS) : IO (RS × Nat) := do
  match scanVar s.buf s.pos with
  | some (x, j) => return ({ s with pos := j }, x)
  | none => if s.eof then s.fail "unexpected end of file" else binNat (← s.refill)

private def binType (s : RS) : IO (RS × Bool) := do
  let (s, x) ← binNat s
  if x == 0 then return (s, false) else if x == 1 then return (s, true)
  else s.fail s!"bad constraint type {x}"

private def checkId (s : RS) (id : Nat) : IO Unit :=
  if id == 0 then s.fail "identifier 0" else pure ()

private partial def readTextStep (s : RS) : IO (RS × Option Step) := do
  let (s, t) ← textTok s true
  match t with
  | .eol => readTextStep s
  | .eof => return (s, none)
  | .word 111 =>
    let (s, id) ← textNat s "identifier"
    checkId s id
    let (s, ty) ← textType s
    let (s, gate) ← textNat s "gate"
    let (s, lits) ← readLits s
    let s ← textEnd s
    return (s, some (.orig id ty gate lits))
  | .word 100 =>
    let (s, ids) ← readIds s
    let s ← textEnd s
    return (s, some (.delete ids))
  | .num false id =>
    checkId s id
    let (s, ty) ← textType s
    let (s, lits) ← readLits s
    let (s, ants) ← readIds s
    let s ← textEnd s
    return (s, some (.derived id ty lits ants))
  | _ => s.fail "unexpected token at start of step"

private partial def readBinStep (s : RS) : IO (RS × Option Step) := do
  if s.pos ≥ s.buf.size then
    if s.eof then return (s, none) else return ← readBinStep (← s.refill)
  let tag := s.buf[s.pos]!
  let s := { s with pos := s.pos + 1 }
  if tag == 111 then
    let (s, id) ← binNat s
    checkId s id
    let (s, ty) ← binType s
    let (s, gate) ← binNat s
    let (s, lits) ← readLits s
    return (s, some (.orig id ty gate lits))
  else if tag == 97 then
    let (s, id) ← binNat s
    checkId s id
    let (s, ty) ← binType s
    let (s, lits) ← readLits s
    let (s, ants) ← readIds s
    return (s, some (.derived id ty lits ants))
  else if tag == 100 then
    let (s, ids) ← readIds s
    return (s, some (.delete ids))
  else s.fail s!"unknown step tag byte {tag}"

private partial def readBlock (s : RS) (maxSteps : Nat) (acc : Array Step) : IO (RS × Array Step) := do
  if acc.size ≥ maxSteps || s.done then return (s, acc)
  let (s, st) ← if s.binary then readBinStep s else readTextStep s
  match st with
  | none => return (s, acc)
  | some (.derived id ty lits ants) =>
    if lits.isEmpty then return ({ s with done := true }, acc.push (.derived id ty lits ants))
    else readBlock s maxSteps (acc.push (.derived id ty lits ants))
  | some st => readBlock s maxSteps (acc.push st)

/-! ### Public API -/

/-- Opens a proof; the binary format is detected by the magic `QLRUPb1\n`. -/
def Reader.open (path : System.FilePath) (chunk : Nat := 1048576) : IO Reader := do
  let h ← IO.FS.Handle.mk path .read
  let chunk := max chunk 1
  let head ← h.read 8
  let binary := head == "QLRUPb1\n".toUTF8
  let st : RS :=
    { h, chunk, binary, buf := if binary then ByteArray.empty else head, base := 0 }
  let st ← if binary then pure { st with base := 8 } else pure st
  return { st := (← IO.mkRef st), binary }

/-- Returns up to `maxSteps` further steps (at least one), `none` at the end of the file,
or an error message. After a derived step without literals, the rest is not read. -/
def Reader.nextBlock (r : Reader) (maxSteps : Nat) : IO (Except String (Option (Array Step))) := do
  let s ← r.st.modifyGet fun s => (s, { s with buf := ByteArray.empty })
  try
    let (s, acc) ← readBlock s (max maxSteps 1) #[]
    r.st.set s
    return .ok (if acc.isEmpty then none else some acc)
  catch e =>
    return .error e.toString

end Qlrup
