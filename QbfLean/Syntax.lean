/-
# Syntax of quantified Boolean formulas (QBF) in prenex CNF form

This file defines *what a QBF is*, syntactically. `QbfLean/Semantics.lean` then says
what it *means*.

We deliberately stay close to QDIMACS and to the Q-resolution literature: a QBF is a
quantifier **prefix** (a list of quantified variables) together with a **matrix** in CNF.
We reuse Lean core's `Std.Sat.CNF` for the matrix, so we inherit its lemmas for free
and stay compatible with the verified LRAT machinery behind `bv_decide`.

Lean notes for newcomers are marked with `NOTE:`.
-/

-- `import` brings another module into scope. `Std.Sat.CNF` is part of Lean core.
import Std.Sat.CNF

/-
NOTE: A `namespace` prefixes every declaration inside it, so `Var` below is really
`Qbf.Var`. It keeps our names from colliding with core/Mathlib names.
-/
namespace Qbf

/-
NOTE: `open X` lets us write `CNF` instead of `Std.Sat.CNF`. It only affects name
resolution in this file — nothing is imported or re-exported.
-/
open Std.Sat

/-! ## Variables and quantifiers -/

/--
Propositional variables are just natural numbers, exactly as in QDIMACS.

NOTE: `abbrev` is a definition marked *reducible*: Lean will silently unfold `Var` to
`Nat` whenever it needs to. So `Var` is not a new type — it is documentation plus a
name to hang notation off. (Use `def` instead if you ever want Lean to keep them
apart, or `structure`/`inductive` for a genuinely distinct type.)
-/
abbrev Var := Nat

/--
The two quantifiers.

NOTE: `inductive` declares a new type by listing its constructors — this is the
standard way to define syntax in Lean. `Quant` has exactly two values, `Quant.ex`
and `Quant.all`.

NOTE: `deriving` asks Lean to generate boilerplate instances automatically:
* `DecidableEq` — an algorithm deciding `q₁ = q₂`, which also lets `decide` and `simp`
  evaluate equalities on `Quant`;
* `Repr` — a printer, so `#eval` can display a `Quant`;
* `Inhabited` — a proof that the type is nonempty, needed by some tactics.
-/
inductive Quant where
  /-- Existential quantifier `∃`. -/
  | ex
  /-- Universal quantifier `∀`. -/
  | all
  deriving DecidableEq, Repr, Inhabited

namespace Quant

/--
Swap `∃` and `∀`. Used when dualising a QBF (`¬∃x. φ ↔ ∀x. ¬φ`).

NOTE: this is defined by *pattern matching on the constructors*. Because `Quant` has
finitely many constructors and we covered them all, Lean accepts the definition as
total — there is no "missing case" possibility.
-/
def dual : Quant → Quant
  | ex => all
  | all => ex

/--
NOTE: `theorem` states and proves a fact. `@[simp]` registers it as a rewrite rule for
the `simp` tactic, so later proofs can use it automatically.

NOTE: the proof `by cases q <;> rfl` reads: split into the two cases for `q`, then in
*each* resulting goal (`<;>` = "apply to all goals") close it by `rfl`, i.e. both sides
compute to the same thing.
-/
@[simp] theorem dual_dual (q : Quant) : q.dual.dual = q := by cases q <;> rfl

end Quant

/-! ## Quantifier prefixes -/

/--
A quantifier prefix: an ordered list of quantified variables, outermost first.

For example `∃x₀ ∀x₁ ∃x₂` is `[(.ex, 0), (.all, 1), (.ex, 2)]`.

NOTE: `Quant × Var` is a *pair* type; its values are written `(q, x)`. The leading dot
in `.ex` is Lean's "expected type" shorthand: since Lean knows the first component must
be a `Quant`, `.ex` means `Quant.ex`.

Design note: we use *named* variables plus an explicit prefix rather than de Bruijn
indices (which is what `Mathlib.ModelTheory.BoundedFormula` does for first-order logic).
De Bruijn gives well-scopedness for free, but Q-resolution, ∀-expansion and QRAT all
talk about named variables and their quantifier level, so named variables keep the
formalisation close to the literature — at the price of having to carry well-formedness
side conditions around by hand (see `QBF.WF` below).
-/
abbrev Prefix := List (Quant × Var)

namespace Prefix

/--
The variables bound by a prefix, in order.

NOTE: `p.map f` is dot notation for `List.map f p`. It works even though `p : Prefix`
rather than `p : List _`, because `Prefix` is an `abbrev` and Lean unfolds it while
looking for the function. `Prod.snd` is the second-projection function `(a, b) ↦ b`.
-/
def vars (p : Prefix) : List Var := p.map Prod.snd

/-
NOTE: these two lemmas let `simp` compute `vars` on concrete prefixes. Both are true
"by definition", which is what `rfl` (reflexivity) means here.
-/
@[simp] theorem vars_nil : vars [] = [] := rfl

@[simp] theorem vars_cons (q : Quant) (x : Var) (p : Prefix) :
    vars ((q, x) :: p) = x :: vars p := rfl

/--
Which quantifier binds `x`, if any. Returns the *outermost* binding, so this is the
intended reading even for a malformed prefix that binds `x` twice.

NOTE: `Option Quant` is either `none` or `some q` — Lean's version of a nullable
result. Returning `Option` instead of a raw `Quant` forces callers to handle the
"unbound variable" case explicitly.
-/
def quantOf : Prefix → Var → Option Quant
  | [], _ => none
  | (q, y) :: p, x => if x = y then some q else quantOf p x

/--
Swap every quantifier in the prefix. Together with negating the matrix this implements
`¬Φ`; see the note at the bottom of `QbfLean/Semantics.lean`.
-/
def dual (p : Prefix) : Prefix := p.map fun qx => (qx.1.dual, qx.2)

/--
NOTE: `List.map_map` collapses `map g (map f p)` into `map (g ∘ f) p`, and here
`Prod.snd ∘ (fun qx => (qx.1.dual, qx.2))` is just `Prod.snd` — so `simp` closes this
without needing an induction.
-/
@[simp] theorem vars_dual (p : Prefix) : vars (dual p) = vars p := by
  simp [dual, vars, List.map_map, Function.comp_def]

end Prefix

/-! ## QBFs -/

/--
A QBF in prenex CNF form (PCNF): a quantifier prefix and a CNF matrix.

NOTE: `structure` declares a record type. It automatically generates the projections
`Φ.pre` and `Φ.matrix`, and lets you build values with anonymous-constructor notation
`⟨p, φ⟩` or with `{ pre := p, matrix := φ }`.

`CNF Var` comes from Lean core: it wraps an `Array` of clauses, where a clause is a
`List (Literal Var)` and `Literal Var = Var × Bool`, with `true` meaning positive
polarity. So the clause `x₀ ∨ ¬x₁` is `[(0, true), (1, false)]`.
-/
structure QBF where
  /-- The quantifier prefix, outermost quantifier first. -/
  pre : Prefix
  /-- The propositional matrix, in CNF. -/
  matrix : CNF Var

namespace QBF

/--
Every variable occurring in the matrix is bound by the prefix, i.e. the QBF is closed.

NOTE: this is a `Prop` (a proposition), not a `Bool`. Propositions are the things you
prove; `Bool`s are the things you compute. `CNF.VarMem v φ` is core's "`v` occurs in
`φ`" predicate.
-/
def Closed (Φ : QBF) : Prop :=
  ∀ v, CNF.VarMem v Φ.matrix → v ∈ Prefix.vars Φ.pre

/--
Well-formedness: the prefix binds each variable at most once, and the QBF is closed.

Almost every theorem about QBF semantics needs one or both halves of this. We keep it
as a separate predicate rather than baking it into the type so that constructing a QBF
(e.g. from a parser) does not require discharging proof obligations up front.
-/
def WF (Φ : QBF) : Prop :=
  (Prefix.vars Φ.pre).Nodup ∧ Φ.Closed

end QBF

/-! ## Making closedness checkable

`QBF.Closed` quantifies over *all* variables (`∀ v : Var, ...`), so Lean cannot decide
it as stated — there are infinitely many `v`. But only the finitely many variables that
actually occur in the matrix matter. Listing them turns the check into a decidable one.
-/

/--
The variables occurring in a CNF, with duplicates.

NOTE: `Array.toList` converts to a list; `List.flatMap f` maps and concatenates. So this
walks every clause and collects the first component (the variable) of every literal.
-/
def cnfVars (φ : CNF Var) : List Var :=
  φ.clauses.toList.flatMap fun c => c.map Prod.fst

/--
Core's `Clause.Mem` is stated as "`(v, false)` or `(v, true)` occurs"; this is the more
convenient "some literal on `v` occurs".
-/
theorem clause_mem_iff (v : Var) (c : CNF.Clause Var) :
    CNF.Clause.Mem v c ↔ ∃ l ∈ c, l.1 = v := by
  constructor
  · rintro (h | h)
    · exact ⟨(v, false), h, rfl⟩
    · exact ⟨(v, true), h, rfl⟩
  · rintro ⟨⟨w, b⟩, hl, rfl⟩
    -- NOTE: `rintro` destructs the literal into `(w, b)` and substitutes `v := w`
    -- via the `rfl` pattern; then the polarity `b` decides which disjunct to pick.
    cases b
    · exact Or.inl hl
    · exact Or.inr hl

theorem varMem_iff_mem_cnfVars (v : Var) (φ : CNF Var) :
    CNF.VarMem v φ ↔ v ∈ cnfVars φ := by
  simp [CNF.VarMem, cnfVars, clause_mem_iff, List.mem_flatMap, List.mem_map]

/--
NOTE: `decidable_of_iff a h` builds a decision procedure for `b` out of one for `a`,
given `h : a ↔ b`. Here `a` is a bounded `∀ v ∈ list, ...`, which Lean can decide by
running down the list.
-/
instance instDecidableClosed (Φ : QBF) : Decidable Φ.Closed :=
  decidable_of_iff (∀ v ∈ cnfVars Φ.matrix, v ∈ Prefix.vars Φ.pre)
    (by simp [QBF.Closed, varMem_iff_mem_cnfVars])

instance instDecidableWF (Φ : QBF) : Decidable Φ.WF :=
  inferInstanceAs (Decidable (_ ∧ _))

end Qbf
