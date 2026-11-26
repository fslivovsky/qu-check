# qu-check

A checker for the QLRUP proofs written by the QBF solver
[miniQU](https://github.com/fslivovsky/miniQU) (`-proof=<file>`; the format is
described in [`doc/proof-format.md`](doc/proof-format.md)), implemented and
verified in Lean 4. Given a QCIR file and a proof, it establishes that the formula is true
(the proof derives the empty term) or false (the proof derives the empty
clause).

```lean
theorem Qlrup.check_true_sound  : check q feed fuel = some true  → q.True
theorem Qlrup.check_false_sound : check q feed fuel = some false → ¬ q.True
```

Here `q : Qcir` is the formula (`parseQcir «contents of the file»`), `q.True`
is its truth as a quantified Boolean formula over a circuit, and `feed` is
*any* source of proof steps. The proofs of the two theorems depend only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Setup

Requires [`elan`](https://github.com/leanprover/elan); `lake` fetches the
toolchain pinned in `lean-toolchain` and the dependencies on the first build.

```bash
git clone https://github.com/fslivovsky/qu-check.git
cd qu-check
lake build
```

The project has no dependencies besides Lean core. The QBF semantics and the
soundness of universal reduction are in `QbfLean/` (see below).

## Usage

There are two ways of checking a proof.

**As a program.** The executable runs the verified checking functions on the
steps of the proof as they are read from the file:

```bash
.lake/build/bin/qlrup-check [--stats] FORMULA.qcir PROOF
```

It prints `s VERIFIED TRUE`, `s VERIFIED FALSE`, or `s NOT VERIFIED: ...`, and
exits with code 0 if the proof was verified. Text and binary proofs are
distinguished automatically.

**As a Lean theorem.** The commands `qlrup_true` and `qlrup_false` run the
same check inside Lean and register the result as a theorem whose statement
contains the contents of the QCIR file:

```lean
import QlrupChecker.Command

qlrup_false php "php.qcir" "php.qlrup"
-- php : ¬ (Qlrup.parseQcir "#QCIR-G14\n...").True
#print axioms php
```

```bash
./qlrup-theorem.sh FORMULA.qcir PROOF [true|false]
```

does this for a pair of files and prints the axioms of the resulting theorem.
The proof is checked while it streams through an opaque constant, so it is
neither stored in the Lean environment nor held in memory as a whole; see
`QlrupChecker/Command.lean` for the design (which follows the streaming import
of [lrat-catcher](https://github.com/leansolving/lrat-catcher)) and for a
discussion of what is trusted.

### Large proofs

Most of the steps in a proof are usually not needed to derive the empty
constraint. `qlrup-trim` (`tools/qlrup-trim.cc` in the miniQU repository)
removes them, and adds
deletion steps so that the checker only keeps the constraints that are still
going to be used:

```bash
qlrup-trim --binary proof.qlrup trimmed.qlrup
./qlrup-theorem.sh formula.qcir trimmed.qlrup
```

The memory used by the check is then bounded by a block of steps plus the
constraints that are alive at the same time.

## What is trusted

- For the theorems `check_true_sound` and `check_false_sound`: the Lean kernel.
- For the meaning of a result: the definitions in `QlrupChecker/Qcir.lean`
  (the QCIR parser, well-formedness, and semantics). This file is short and
  does not depend on the rest of the checker. It imports the definitions of
  quantifier prefixes and assignments from `QbfLean/Syntax.lean` and
  `QbfLean/Semantics.lean`.
- For a theorem produced by `qlrup_true` or `qlrup_false`: additionally the
  Lean compiler (one `native_decide` axiom), and the reader that turns the proof
  file into steps, to the extent discussed in `Command.lean`. The reader is not
  trusted to parse correctly, because the check is sound for every sequence of
  steps.
- For the output of the `qlrup-check` executable: the Lean compiler, and the
  loop in `Main.lean`, which applies the verified function `runBlock` to
  successive blocks of steps. This loop is not covered by a theorem.

The solver, the trimmer, and the construction of the extended prefix
(`mkCtx`) are not trusted.

## How it works

| File | |
|---|---|
| `QbfLean/Syntax.lean`, `QbfLean/Semantics.lean` | **Trusted** (the parts used by `Qcir.lean`). Quantifier prefixes, assignments, and the semantics of a prefix (`evalPrefix`). |
| `QbfLean/QRes.lean` | Q-resolution and the soundness of universal reduction (`Qbf.evalPrefix_reduce`). |
| `Qcir.lean` | **Trusted.** Formulas, parser, semantics. |
| `Tseitin.lean` | The Tseitin encoding `q.tseitin`. An *extended prefix* quantifies the variables of gates existentially, after the variables and gates they depend on. `tseitin_evalPrefix`: if `q` is true, so is its encoding under any extended prefix. |
| `Derive.lean` | Resolution and universal reduction on sets of literals. Soundness of reduction is `Qbf.evalPrefix_reduce` from `QbfLean/QRes.lean`. |
| `Check.lean` | Checks for original clauses (a clause of the encoding, possibly with additional literals) and derived clauses (a chain of resolution steps on arbitrary pivots followed by reduction; if that fails, the chain is tried again with reduction after every step). Invariant: if the encoding is true under the extended prefix, then so is a CNF that implies it and all clauses derived so far. |
| `Ext.lean` | Computes the extended prefix that places the variable of a gate right after the innermost quantifier block the gate depends on. The construction is not verified; instead `ctxOk` tests the result, and `ctxOk_sound` proves the test correct. |
| `Run.lean` | The checker for a sequence of blocks of steps, and the main theorems. Terms are checked as clauses of the *dual* formula (quantifiers swapped, output negated): a term of `q` is the negation of a clause of `q.dual`, and `q` is true iff `q.dual` is false (`Qcir.dual_true`). |
| `Reader.lean` | Reads steps from text and binary proof files. Not verified. |
| `Command.lean` | `qlrup_true` and `qlrup_false`. |

Resolution is allowed on universal pivots (and term resolution on existential
ones), so the proofs of the QU-resolution mode of miniQU can be checked as well
as those of the Q-resolution mode.

## Restrictions

- Gates must be defined before they are used, and quantifiers must precede
  gate definitions. (miniQU itself accepts gates in any order.)
- Constraints must not contain complementary literals, so proofs with
  long-distance resolution (mode 2 of miniQU) cannot be checked.
- Memory use is roughly ten times the size of the QCIR file plus the
  constraints that are alive, so formulas of several hundred megabytes need
  many gigabytes.

## Tests

```bash
MINIQU_REPO=/path/to/miniQU ./test.sh 1 40
```

generates random instances with the scripts in the `tests` directory of a
miniQU checkout, runs miniQU (`$MINIQU`, by default
`$MINIQU_REPO/build/release/bin/miniQU`) with proof logging in several
configurations, and compares the result of the checker with the reference
checker `tests/qlrup_check.py` of miniQU, also on corrupted proofs.
