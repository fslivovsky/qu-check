/-
# Q-resolution

The classical proof system for **refuting** false QBFs (Kleine Büning–Karpinski–Flögel).
A derivation manipulates clauses; deriving the empty clause certifies that the QBF is
false — that the universal player wins.

Three rules:

* **axiom** — take a (non-tautological) clause of the matrix;
* **∃-resolution** — resolve two clauses on an *existential* pivot; the resolvent must be
  non-tautological;
* **∀-reduction** — drop a *universal* literal on `u` from a clause `C`, provided every
  existential variable of `C` is quantified to the *left* of `u`.

Rule 3 is the only one carrying QBF content — it is not propositionally sound, and its
soundness is exactly where the quantifier order matters. Everything else is ordinary
propositional resolution.

This file lands the definitions, the datatype, and the full soundness theorem
`QRes.sound`. The two propositional rules go through a monotonicity argument
(`evalPrefix_mono`); the ∀-reduction step is isolated in `evalPrefix_reduce`, whose
proof pairs each play of the game with a deviated play in which the universal player
falsifies the reduced literal (`evalPrefix_erase_pair`). Soundness holds only for
prefixes without repeated binders — see the counterexamples at the ∀-reduction section
for why the `Nodup` hypothesis (and the non-tautology premise of the rules) cannot be
dropped.
-/

import QbfLean.Semantics

namespace Qbf

open Std.Sat

/-! ## Prefix order

`∀`-reduction needs to compare quantifier depths: a universal literal on `u` may be
dropped only when every existential variable still in the clause sits to `u`'s left.
-/

/--
The depth of `x` in the prefix: the position of its (first) binder, or `p.length` if `x`
is unbound. Under `QBF.WF` (no repeated binders) this is the honest quantifier level.

NOTE: `List.findIdx` returns the index of the first element passing the predicate.
-/
def Prefix.level (p : Prefix) (x : Var) : Nat := (Prefix.vars p).findIdx (· == x)

/-- `x` is quantified strictly to the left of `y`. -/
def Prefix.before (p : Prefix) (x y : Var) : Prop := p.level x < p.level y

/-- The order side conditions of the rules are checkable: `before` is just `<` on `Nat`.

NOTE: `inferInstanceAs` asks typeclass resolution for an instance of a *definitionally
equal* type — needed because `before` is a `def` the resolver will not unfold on its
own. -/
instance instDecidableBefore (p : Prefix) (x y : Var) : Decidable (p.before x y) :=
  inferInstanceAs (Decidable (_ < _))

/-! Basic facts about `level`, `before` and `quantOf`, used to push the ∀-reduction
side conditions through an induction on the prefix. -/

@[simp] theorem Prefix.level_cons_self (q : Quant) (x : Var) (p : Prefix) :
    Prefix.level ((q, x) :: p) x = 0 := by
  simp [Prefix.level, List.findIdx_cons]

theorem Prefix.level_cons_ne {x y : Var} (q : Quant) (p : Prefix) (h : y ≠ x) :
    Prefix.level ((q, y) :: p) x = Prefix.level p x + 1 := by
  -- NOTE: `y == x` is the `Bool`-valued test, so the hypothesis `y ≠ x` must be fed to
  -- `simp` in its `Bool` form `(y == x) = false`.
  simp [Prefix.level, List.findIdx_cons, beq_eq_false_iff_ne.mpr h]

/-- Peeling a binder on a *different* variable off the prefix does not change the
relative order of `x` and `y`. -/
theorem Prefix.before_cons_ne {x y z : Var} (q : Quant) (p : Prefix)
    (hx : x ≠ z) (hy : y ≠ z) :
    Prefix.before ((q, z) :: p) x y ↔ Prefix.before p x y := by
  unfold Prefix.before
  rw [Prefix.level_cons_ne q p (Ne.symm hx), Prefix.level_cons_ne q p (Ne.symm hy)]
  omega

/-- A variable with a quantifier is bound by the prefix. -/
theorem Prefix.mem_vars_of_quantOf :
    ∀ {p : Prefix} {x : Var} {q : Quant}, p.quantOf x = some q → x ∈ Prefix.vars p
  | [], _, _, h => nomatch h
  | (_, y) :: p, x, _, h => by
      rw [Prefix.vars_cons, List.mem_cons]
      by_cases hxy : x = y
      · exact Or.inl hxy
      · simp only [Prefix.quantOf, if_neg hxy] at h
        exact Or.inr (Prefix.mem_vars_of_quantOf h)

@[simp] theorem Prefix.vars_append (p₁ p₂ : Prefix) :
    Prefix.vars (p₁ ++ p₂) = Prefix.vars p₁ ++ Prefix.vars p₂ :=
  List.map_append ..

/-- A variable bound in the first part of a prefix has level below that part's length. -/
theorem Prefix.level_append_of_mem :
    ∀ {p₁ : Prefix} (p₂ : Prefix) {x : Var}, x ∈ Prefix.vars p₁ →
      Prefix.level (p₁ ++ p₂) x < p₁.length
  | [], _, _, hx => absurd hx (by simp)
  | (q, y) :: p₁, p₂, x, hx => by
      rw [List.cons_append]
      by_cases hyx : y = x
      · subst hyx
        rw [Prefix.level_cons_self]
        simp
      · rw [Prefix.level_cons_ne q _ hyx, List.length_cons]
        rw [Prefix.vars_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd rfl hyx
        · exact Nat.succ_lt_succ (Prefix.level_append_of_mem p₂ hx)

/-- A variable *not* bound in the first part has its level offset past it. -/
theorem Prefix.level_append_of_not_mem :
    ∀ {p₁ : Prefix} (p₂ : Prefix) {x : Var}, x ∉ Prefix.vars p₁ →
      Prefix.level (p₁ ++ p₂) x = p₁.length + Prefix.level p₂ x
  | [], _, _, _ => by simp
  | (q, y) :: p₁, p₂, x, hx => by
      rw [Prefix.vars_cons, List.mem_cons, not_or] at hx
      rw [List.cons_append, Prefix.level_cons_ne q _ (fun h => hx.1 h.symm),
        Prefix.level_append_of_not_mem p₂ hx.2, List.length_cons]
      omega

theorem Prefix.before_trans {p : Prefix} {x y z : Var}
    (h₁ : p.before x y) (h₂ : p.before y z) : p.before x z := Nat.lt_trans h₁ h₂

theorem Prefix.before_asymm {p : Prefix} {x y : Var} (h : p.before x y) :
    ¬ p.before y x := by
  unfold Prefix.before at *
  omega

/-- Every bound variable has a quantifier. -/
theorem Prefix.exists_quantOf_of_mem :
    ∀ {p : Prefix} {x : Var}, x ∈ Prefix.vars p → ∃ q, p.quantOf x = some q
  | [], _, hx => absurd hx (by simp)
  | (q, y) :: p, x, hx => by
      by_cases hxy : x = y
      · exact ⟨q, by simp [Prefix.quantOf, hxy]⟩
      · rw [Prefix.vars_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd rfl hxy
        · obtain ⟨q', hq'⟩ := Prefix.exists_quantOf_of_mem hx
          exact ⟨q', by simp [Prefix.quantOf, hxy, hq']⟩

/-- A variable whose level is inside the prefix is bound by it. -/
theorem Prefix.mem_vars_of_level_lt :
    ∀ {p : Prefix} {x : Var}, Prefix.level p x < p.length → x ∈ Prefix.vars p
  | [], _, h => absurd h (by simp)
  | (q, y) :: p, x, h => by
      by_cases hyx : y = x
      · subst hyx
        simp
      · rw [Prefix.level_cons_ne q p hyx, List.length_cons] at h
        rw [Prefix.vars_cons]
        exact List.mem_cons_of_mem _ (Prefix.mem_vars_of_level_lt (by omega))

/-- On a duplicate-free prefix, levels identify bound variables. -/
theorem Prefix.eq_of_level_eq :
    ∀ {p : Prefix}, (Prefix.vars p).Nodup → ∀ {x y : Var},
      x ∈ Prefix.vars p → y ∈ Prefix.vars p →
      Prefix.level p x = Prefix.level p y → x = y
  | [], _, x, _, hx, _, _ => absurd hx (by simp)
  | (q, z) :: p, hnd, x, y, hx, hy, h => by
      rw [Prefix.vars_cons, List.nodup_cons] at hnd
      rw [Prefix.vars_cons, List.mem_cons] at hx hy
      by_cases hzx : z = x <;> by_cases hzy : z = y
      · rw [← hzx, ← hzy]
      · rcases hy with rfl | hy
        · exact absurd rfl hzy
        · rw [← hzx, Prefix.level_cons_self, Prefix.level_cons_ne q p hzy] at h
          exact absurd h.symm (by omega)
      · rcases hx with rfl | hx
        · exact absurd rfl hzx
        · rw [Prefix.level_cons_ne q p hzx, ← hzy, Prefix.level_cons_self] at h
          exact absurd h (by omega)
      · rcases hx with rfl | hx
        · exact absurd rfl hzx
        rcases hy with rfl | hy
        · exact absurd rfl hzy
        rw [Prefix.level_cons_ne q p hzx, Prefix.level_cons_ne q p hzy] at h
        exact Prefix.eq_of_level_eq hnd.2 hx hy (by omega)

/-- Split a prefix at the (outermost) binder `quantOf` reports. -/
theorem Prefix.exists_split_of_quantOf :
    ∀ {p : Prefix} {x : Var} {q : Quant}, p.quantOf x = some q →
      ∃ p₁ p₂, p = p₁ ++ (q, x) :: p₂ ∧ x ∉ Prefix.vars p₁
  | [], _, _, h => nomatch h
  | (q', y) :: p, x, q, h => by
      by_cases hxy : x = y
      · subst hxy
        obtain rfl : q' = q := by simpa [Prefix.quantOf] using h
        exact ⟨[], p, rfl, by simp⟩
      · have h' : Prefix.quantOf p x = some q := by simpa [Prefix.quantOf, hxy] using h
        obtain ⟨p₁, p₂, rfl, hx⟩ := Prefix.exists_split_of_quantOf h'
        refine ⟨(q', y) :: p₁, p₂, rfl, ?_⟩
        rw [Prefix.vars_cons, List.mem_cons, not_or]
        exact ⟨hxy, hx⟩

/-- The binder `quantOf` reports occurs in the prefix. -/
theorem Prefix.mem_of_quantOf {p : Prefix} {x : Var} {q : Quant}
    (h : p.quantOf x = some q) : (q, x) ∈ p := by
  obtain ⟨p₁, p₂, rfl, -⟩ := Prefix.exists_split_of_quantOf h
  exact List.mem_append_right _ (List.mem_cons_self ..)

/--
On a prefix without repeated binders, `quantOf` recovers the quantifier of any binding
that occurs in it. This is where a duplicate binding would lie: `quantOf` reports the
*outermost* binder, which need not be the one at hand.
-/
theorem Prefix.quantOf_of_mem :
    ∀ {p : Prefix}, (Prefix.vars p).Nodup →
      ∀ {q : Quant} {x : Var}, (q, x) ∈ p → p.quantOf x = some q
  | [], _, _, _, h => nomatch h
  | (q', y) :: p, hnd, q, x, h => by
      rw [Prefix.vars_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h with heq | htail
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        simp [Prefix.quantOf]
      · have hx : x ∈ Prefix.vars p := List.mem_map.mpr ⟨(q, x), htail, rfl⟩
        have hxy : x ≠ y := fun hxy => hnd.1 (hxy ▸ hx)
        simp only [Prefix.quantOf, if_neg hxy]
        exact Prefix.quantOf_of_mem hnd.2 htail

/-! ## Clauses

We reuse core's `CNF.Clause Var = List (Literal Var)` with `Literal Var = Var × Bool`
(`true` = positive polarity). A handful of operations on top.
-/

/-- The variables occurring in a clause (with multiplicity). -/
def clauseVars (C : CNF.Clause Var) : List Var := C.map Prod.fst

/-- A clause is tautological when some variable occurs both positively and negatively.
(Read conjunctively, the same predicate on a *cube* means it is contradictory.) -/
def Taut (C : CNF.Clause Var) : Prop := ∃ v, (v, true) ∈ C ∧ (v, false) ∈ C

/-- `Taut` quantifies over all of `Var`, but only the literals of `C` can witness it:
a clause is tautological iff it contains some literal together with its complement. -/
theorem taut_iff {C : CNF.Clause Var} : Taut C ↔ ∃ l ∈ C, (l.1, !l.2) ∈ C := by
  constructor
  · rintro ⟨v, h1, h2⟩
    exact ⟨(v, true), h1, h2⟩
  · rintro ⟨⟨v, c⟩, hl, hl'⟩
    cases c
    · exact ⟨v, hl', hl⟩
    · exact ⟨v, hl, hl'⟩

/-- The bounded reformulation makes the rules' non-tautology side condition checkable
(compare `Qbf.instDecidableClosed`). -/
instance instDecidableTaut (C : CNF.Clause Var) : Decidable (Taut C) :=
  decidable_of_iff _ taut_iff.symm

/-- Delete every literal on `u` from `C`. -/
def eraseVar (C : CNF.Clause Var) (u : Var) : CNF.Clause Var := C.filter (fun l => l.1 != u)

/-- The Q-resolvent on pivot `x`: drop `x` from both clauses and concatenate. -/
def resolvent (C₁ C₂ : CNF.Clause Var) (x : Var) : CNF.Clause Var :=
  eraseVar C₁ x ++ eraseVar C₂ x

/-! ## Derivations

`QRes Φ C` means "`C` is Q-derivable from `Φ`". A refutation is a derivation of `[]`.
-/

/-- Q-resolution derivability. -/
inductive QRes (Φ : QBF) : CNF.Clause Var → Prop
  /-- A non-tautological matrix clause. -/
  | ax {C : CNF.Clause Var} (hmem : C ∈ Φ.matrix.clauses) (hnt : ¬ Taut C) : QRes Φ C
  /-- Resolution on an existential pivot `x`; the resolvent must stay non-tautological. -/
  | res {C₁ C₂ : CNF.Clause Var} {x : Var}
      (h₁ : QRes Φ C₁) (h₂ : QRes Φ C₂)
      (hx : Φ.pre.quantOf x = some Quant.ex)
      (hx₁ : (x, true) ∈ C₁) (hx₂ : (x, false) ∈ C₂)
      (hnt : ¬ Taut (resolvent C₁ C₂ x)) :
      QRes Φ (resolvent C₁ C₂ x)
  /-- Reduce the universal variable `u`, all existentials of `C` being to its left. -/
  | red {C : CNF.Clause Var} {u : Var}
      (h : QRes Φ C)
      (hu : Φ.pre.quantOf u = some Quant.all)
      (hlvl : ∀ e ∈ clauseVars C, Φ.pre.quantOf e = some Quant.ex → Φ.pre.before e u) :
      QRes Φ (eraseVar C u)

/-- A refutation: a derivation of the empty clause. -/
def QBF.Refutes (Φ : QBF) : Prop := QRes Φ ([] : CNF.Clause Var)

/-! ## Every derived clause is non-tautological

A small invariant, needed for propositional resolution soundness (it rules out the pivot
appearing with both polarities in a parent).
-/

theorem QRes.not_taut {Φ : QBF} {C : CNF.Clause Var} (h : QRes Φ C) : ¬ Taut C := by
  induction h with
  | ax _ hnt => exact hnt
  | res _ _ _ _ _ hnt => exact hnt
  | red _ _ _ ih =>
      -- Erasing literals cannot manufacture a tautology.
      rintro ⟨v, hv1, hv2⟩
      exact ih ⟨v, (List.mem_filter.mp hv1).1, (List.mem_filter.mp hv2).1⟩

/-! ## Monotonicity of `evalPrefix` in the matrix

If matrix `ψ₁` entails `ψ₂` clause-wise, then `∃` winning `ψ₁` implies `∃` winning `ψ₂`:
the very same play works. This is the engine behind the two propositional rules.
-/

theorem evalPrefix_mono (p : Prefix) (ψ₁ ψ₂ : CNF Var)
    (h : ∀ τ, CNF.eval τ ψ₁ = true → CNF.eval τ ψ₂ = true) (σ : Assignment) :
    evalPrefix p σ ψ₁ → evalPrefix p σ ψ₂ := by
  induction p generalizing σ with
  | nil => simp only [evalPrefix_nil]; exact h σ
  | cons qx p ih =>
      obtain ⟨q, x⟩ := qx
      cases q with
      | ex => simp only [evalPrefix_ex]; rintro ⟨b, hb⟩; exact ⟨b, ih _ hb⟩
      | all => simp only [evalPrefix_all]; intro hb b; exact ih _ (hb b)

/-- Matrices with the same truth on every assignment are interchangeable for `evalPrefix`. -/
theorem evalPrefix_eval_congr (p : Prefix) (σ : Assignment) (ψ₁ ψ₂ : CNF Var)
    (h : ∀ τ, CNF.eval τ ψ₁ = CNF.eval τ ψ₂) : evalPrefix p σ ψ₁ ↔ evalPrefix p σ ψ₂ :=
  ⟨evalPrefix_mono p ψ₁ ψ₂ (fun τ h' => by rw [← h τ]; exact h') σ,
   evalPrefix_mono p ψ₂ ψ₁ (fun τ h' => by rw [h τ]; exact h') σ⟩

/-- An unsatisfiable matrix cannot be won by `∃`. -/
theorem not_evalPrefix_of_unsat (p : Prefix) (σ : Assignment) (ψ : CNF Var)
    (h : ∀ τ, CNF.eval τ ψ = false) : ¬ evalPrefix p σ ψ := by
  induction p generalizing σ with
  | nil => simp only [evalPrefix_nil, h σ]; exact Bool.false_ne_true
  | cons qx p ih =>
      obtain ⟨q, x⟩ := qx
      cases q with
      | ex => simp only [evalPrefix_ex]; rintro ⟨b, hb⟩; exact ih _ hb
      | all => simp only [evalPrefix_all]; intro hb; exact ih _ (hb false)

/-- A clause of a true CNF is satisfied by any assignment that satisfies the CNF. -/
theorem clause_eval_of_mem {τ : Assignment} {C : CNF.Clause Var} {f : CNF Var}
    (hC : C ∈ f.clauses) (h : CNF.eval τ f = true) : CNF.Clause.eval τ C = true := by
  rw [CNF.eval, Array.all_eq_true_iff_forall_mem] at h
  exact h C hC

/-! ## Propositional soundness of resolution

A clause is satisfied iff one of its literals is; membership in `eraseVar` / `resolvent`
is characterised below, and then the standard resolution argument goes through by casing
on the pivot's value. Non-tautology of the parents rules out the pivot's other polarity.
-/

/-- A clause is true under `τ` iff some literal of it is. -/
theorem clause_eval_iff {τ : Assignment} {C : CNF.Clause Var} :
    CNF.Clause.eval τ C = true ↔ ∃ l ∈ C, τ l.1 = l.2 := by
  simp only [CNF.Clause.eval, List.any_eq_true, beq_iff_eq]

/-- Membership in `eraseVar`: keep the literal, drop the variable. -/
theorem mem_eraseVar {l : Literal Var} {C : CNF.Clause Var} {u : Var} :
    l ∈ eraseVar C u ↔ l ∈ C ∧ l.1 ≠ u := by
  rw [eraseVar, List.mem_filter, bne_iff_ne]

/-- Membership in `clauseVars`: some literal of the clause carries the variable. -/
theorem mem_clauseVars {v : Var} {C : CNF.Clause Var} :
    v ∈ clauseVars C ↔ ∃ l ∈ C, l.1 = v := by
  simp [clauseVars]

/-- A tautology stays one in any superclause. (Contrapositive: subclauses of
non-tautological clauses are non-tautological.) -/
theorem Taut.mono {C C' : CNF.Clause Var} (hsub : C ⊆ C') : Taut C → Taut C'
  | ⟨v, h1, h2⟩ => ⟨v, hsub h1, hsub h2⟩

theorem eraseVar_mono {C C' : CNF.Clause Var} {u : Var} (h : C ⊆ C') :
    eraseVar C u ⊆ eraseVar C' u := fun _l hl =>
  mem_eraseVar.mpr ⟨h (mem_eraseVar.mp hl).1, (mem_eraseVar.mp hl).2⟩

theorem resolvent_mono {C₁ C₂ D₁ D₂ : CNF.Clause Var} {x : Var}
    (h₁ : C₁ ⊆ D₁) (h₂ : C₂ ⊆ D₂) : resolvent C₁ C₂ x ⊆ resolvent D₁ D₂ x := by
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact List.mem_append_left _ (eraseVar_mono h₁ hl)
  · exact List.mem_append_right _ (eraseVar_mono h₂ hl)

/-- Resolution is propositionally sound: a common satisfying assignment of both
non-tautological parents satisfies the resolvent. -/
theorem resolvent_sound {τ : Assignment} {C₁ C₂ : CNF.Clause Var} {x : Var}
    (ht₁ : ¬ Taut C₁) (ht₂ : ¬ Taut C₂)
    (hx₁ : ((x, true) : Literal Var) ∈ C₁) (hx₂ : ((x, false) : Literal Var) ∈ C₂)
    (e₁ : CNF.Clause.eval τ C₁ = true) (e₂ : CNF.Clause.eval τ C₂ = true) :
    CNF.Clause.eval τ (resolvent C₁ C₂ x) = true := by
  rw [resolvent, clause_eval_iff]
  rw [clause_eval_iff] at e₁ e₂
  obtain ⟨⟨v₁, b₁⟩, hm₁, hs₁⟩ := e₁
  obtain ⟨⟨v₂, b₂⟩, hm₂, hs₂⟩ := e₂
  dsimp only at hs₁ hs₂
  cases hx : τ x with
  | false =>
    -- `x` is false, so a *different* literal of `C₁` carries it; it survives erasure.
    have hvx : v₁ ≠ x := by
      intro heq
      have hb : b₁ = false := by rw [← hs₁, heq]; exact hx
      exact ht₁ ⟨x, hx₁, heq ▸ hb ▸ hm₁⟩
    exact ⟨(v₁, b₁), List.mem_append_left _ (mem_eraseVar.mpr ⟨hm₁, hvx⟩), hs₁⟩
  | true =>
    have hvx : v₂ ≠ x := by
      intro heq
      have hb : b₂ = true := by rw [← hs₂, heq]; exact hx
      exact ht₂ ⟨x, heq ▸ hb ▸ hm₂, hx₂⟩
    exact ⟨(v₂, b₂), List.mem_append_right _ (mem_eraseVar.mpr ⟨hm₂, hvx⟩), hs₂⟩

/-! ## ∀-reduction: the one QBF-specific lemma

This is the heart of Q-resolution soundness and the only rule that is not propositionally
valid. Dropping the universal literal on `u` is justified because, when the universal
player reaches `u`, it can set `u` to falsify that literal — and every existential of the
clause is already fixed (they sit to `u`'s left), so the rest of the clause must carry the
weight.

Two hypotheses beyond the rule's side conditions are *essential*, not conveniences —
without either the statement is false:

* `¬ Taut C`. Counterexample: prefix `∀u`, `C = u ∨ ¬u`, `Ψ` empty. The left-hand side
  holds (`C` is a tautology) but `eraseVar C u = []` deletes *both* polarities at once,
  and the right-hand side asserts the empty clause. Erasure only mimics the textbook
  rule — dropping literals of a single polarity — on non-tautological clauses.
* `Nodup`. Counterexample: the malformed prefix `∀u ∃u`, `C = u`, `Ψ` empty. `quantOf`
  reports the outermost binder `∀`, but the *inner*, existential binder controls `u`'s
  final value, so the left-hand side holds while the right-hand side again asserts the
  empty clause. This is where the no-duplicate-binder half of `QBF.WF` genuinely earns
  its keep.

The proof pairs each play of the game against a *deviated* play in which the universal
player, on reaching `u`, picks the value falsifying `C`'s `u`-literal instead. The two
plays agree on everything that matters to `C`: its existential variables are set before
`u` (the level condition), its universal variables are fed the same moves, and only the
existential moves *after* `u` may drift — but those never occur in `C`. In the deviated
play `C` is true with its `u`-literal false, so a surviving literal of `eraseVar C u` is
true there, hence also in the real play; the rest of the matrix `Ψ` is true in the real
play outright.

There is no shortcut around carrying both plays: `Ψ` is arbitrary (at the call site it
is `Φ.matrix ++ D`, which may mention `u`), so nothing evaluated in the deviated play can
be transported back wholesale — only the `u`-free surviving literal can.
-/

/--
The paired-plays kernel of ∀-reduction, for the part `p` of the prefix *after* `u`'s
binder. `σ₁` is the current position of the deviated play (where `C`'s `u`-literal is
false), `σ₂` of the real play; they agree on the variables of `C` other than `u`. If
both plays are ∃-winnable with `C` in the matrix, the real one is ∃-winnable with
`eraseVar C u` instead.

The hypotheses record exactly what survives past `u`'s binder: `u` itself is not
re-bound, and no variable of `C` is bound existentially (they all sit to `u`'s left).

NOTE: at a `∀`-binder both hypotheses are instantiated with the *same* move, keeping the
plays in lockstep; at an `∃`-binder each play brings its own witness and the agreement
invariant survives because the bound variable is not in `C`.
-/
theorem evalPrefix_erase_pair {C : CNF.Clause Var} {u : Var} :
    ∀ (p : Prefix) (σ₁ σ₂ : Assignment) (Ψ : CNF Var),
      u ∉ Prefix.vars p →
      (∀ e ∈ clauseVars C, (Quant.ex, e) ∉ p) →
      (∀ v ∈ clauseVars C, v ≠ u → σ₁ v = σ₂ v) →
      (∀ c, ((u, c) : Literal Var) ∈ C → σ₁ u ≠ c) →
      evalPrefix p σ₁ (Ψ.add C) → evalPrefix p σ₂ (Ψ.add C) →
      evalPrefix p σ₂ (Ψ.add (eraseVar C u))
  | [], σ₁, σ₂, Ψ, _, _, hagree, hfal, h₁, h₂ => by
      simp only [evalPrefix_nil, CNF.eval_add, Bool.and_eq_true] at h₁ h₂ ⊢
      refine ⟨?_, h₂.2⟩
      -- In the deviated play some literal of `C` is true, and it cannot be on `u`.
      obtain ⟨⟨v, c⟩, hmem, hval⟩ := clause_eval_iff.mp h₁.1
      have hvu : v ≠ u := by
        rintro rfl
        exact hfal c hmem hval
      refine clause_eval_iff.mpr ⟨(v, c), mem_eraseVar.mpr ⟨hmem, hvu⟩, ?_⟩
      show σ₂ v = c
      rw [← hagree v (mem_clauseVars.mpr ⟨(v, c), hmem, rfl⟩) hvu]
      exact hval
  | (.ex, y) :: p, σ₁, σ₂, Ψ, hu, hex, hagree, hfal, h₁, h₂ => by
      rw [Prefix.vars_cons, List.mem_cons, not_or] at hu
      obtain ⟨huy, hup⟩ := hu
      simp only [evalPrefix_ex] at h₁ h₂ ⊢
      obtain ⟨b₁, h₁⟩ := h₁
      obtain ⟨b₂, h₂⟩ := h₂
      -- Each play keeps its own existential witness; `y ∉ C` keeps them interchangeable.
      refine ⟨b₂, evalPrefix_erase_pair p σ₁[y ↦ b₁] σ₂[y ↦ b₂] Ψ hup
        (fun e he hmem => hex e he (List.mem_cons_of_mem _ hmem)) ?_ ?_ h₁ h₂⟩
      · intro v hv hvu
        have hvy : v ≠ y := by
          rintro rfl
          exact hex v hv (List.mem_cons_self ..)
        rw [Assignment.set_other _ _ hvy, Assignment.set_other _ _ hvy]
        exact hagree v hv hvu
      · intro c hc
        rw [Assignment.set_other _ _ huy]
        exact hfal c hc
  | (.all, y) :: p, σ₁, σ₂, Ψ, hu, hex, hagree, hfal, h₁, h₂ => by
      rw [Prefix.vars_cons, List.mem_cons, not_or] at hu
      obtain ⟨huy, hup⟩ := hu
      simp only [evalPrefix_all] at h₁ h₂ ⊢
      intro b
      -- Lockstep: the same universal move is fed to both plays.
      refine evalPrefix_erase_pair p σ₁[y ↦ b] σ₂[y ↦ b] Ψ hup
        (fun e he hmem => hex e he (List.mem_cons_of_mem _ hmem)) ?_ ?_ (h₁ b) (h₂ b)
      · intro v hv hvu
        by_cases hvy : v = y
        · subst hvy; simp
        · rw [Assignment.set_other _ _ hvy, Assignment.set_other _ _ hvy]
          exact hagree v hv hvu
      · intro c hc
        rw [Assignment.set_other _ _ huy]
        exact hfal c hc

/--
**Soundness of ∀-reduction.** Stated over a bare prefix (rather than a `QBF`) so that
the induction walking down to `u`'s binder goes through; the two cons-cases before `u`
just push the side conditions into the tail, and the case *at* `u`'s binder instantiates
the universal move once with the falsifying value `b₀` and once with the actual move,
handing both branches to `evalPrefix_erase_pair`.

NOTE: the base case is vacuous — an empty prefix cannot satisfy `quantOf u = some .all`.
The clause-side content of the rule lives entirely in the leaf of the pairing lemma.
-/
theorem evalPrefix_reduce {C : CNF.Clause Var} {u : Var} (hnt : ¬ Taut C) :
    ∀ (p : Prefix), (Prefix.vars p).Nodup →
      p.quantOf u = some Quant.all →
      (∀ e ∈ clauseVars C, p.quantOf e = some Quant.ex → p.before e u) →
      ∀ (σ : Assignment) (Ψ : CNF Var),
        evalPrefix p σ (Ψ.add C) → evalPrefix p σ (Ψ.add (eraseVar C u))
  | [], _, hu, _, _, _ => nomatch hu
  | (q, y) :: p, hnd, hu, hlvl, σ, Ψ => by
      rw [Prefix.vars_cons, List.nodup_cons] at hnd
      obtain ⟨hy, hnd'⟩ := hnd
      by_cases hyu : y = u
      · -- At `u`'s binder. Its quantifier must be the recorded one, `∀`.
        subst hyu
        have hq : q = Quant.all := by simpa [Prefix.quantOf] using hu
        subst hq
        -- The value falsifying every `y`-literal of `C`; `¬ Taut C` makes one exist.
        obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Bool, ∀ c, ((y, c) : Literal Var) ∈ C → b₀ ≠ c := by
          by_cases ht : ((y, true) : Literal Var) ∈ C
          · refine ⟨false, fun c hc => ?_⟩
            cases c
            · exact absurd ⟨y, ht, hc⟩ hnt
            · exact Bool.false_ne_true
          · refine ⟨true, fun c hc => ?_⟩
            cases c
            · exact fun h => Bool.false_ne_true h.symm
            · exact absurd hc ht
        -- No variable of `C` may be bound existentially after `u`: its (unique) binder
        -- would sit at level `≥` that of `u`, contradicting the level condition.
        have hnotex : ∀ e ∈ clauseVars C, (Quant.ex, e) ∉ p := by
          intro e he hmem
          have hev : e ∈ Prefix.vars p := List.mem_map.mpr ⟨(Quant.ex, e), hmem, rfl⟩
          have hey : e ≠ y := fun h => hy (h ▸ hev)
          have hq : Prefix.quantOf p e = some Quant.ex := Prefix.quantOf_of_mem hnd' hmem
          have hbef := hlvl e he (by simpa [Prefix.quantOf, hey] using hq)
          simp only [Prefix.before, Prefix.level_cons_self] at hbef
          exact Nat.not_lt_zero _ hbef
        simp only [evalPrefix_all]
        intro h b
        refine evalPrefix_erase_pair p σ[y ↦ b₀] σ[y ↦ b] Ψ hy hnotex ?_ ?_ (h b₀) (h b)
        · intro v _ hvu
          rw [Assignment.set_other _ _ hvu, Assignment.set_other _ _ hvu]
        · intro c hc
          rw [Assignment.set_same]
          exact hb₀ c hc
      · -- Before `u`'s binder: push every hypothesis into the tail and recurse.
        have hu' : Prefix.quantOf p u = some Quant.all := by
          simpa [Prefix.quantOf, Ne.symm hyu] using hu
        have hlvl' : ∀ e ∈ clauseVars C,
            Prefix.quantOf p e = some Quant.ex → Prefix.before p e u := by
          intro e he hq
          have hey : e ≠ y := by
            rintro rfl
            exact hy (Prefix.mem_vars_of_quantOf hq)
          have hbef := hlvl e he (by simpa [Prefix.quantOf, hey] using hq)
          rwa [Prefix.before_cons_ne q p hey (Ne.symm hyu)] at hbef
        cases q with
        | ex =>
            simp only [evalPrefix_ex]
            rintro ⟨b, hb⟩
            exact ⟨b, evalPrefix_reduce hnt p hnd' hu' hlvl' _ Ψ hb⟩
        | all =>
            simp only [evalPrefix_all]
            intro h b
            exact evalPrefix_reduce hnt p hnd' hu' hlvl' _ Ψ (h b)

/-! ## Soundness

The invariant is that adding a derived clause `C` on top of the matrix — *and any further
clauses `D`* — preserves ∃-provability. Generalising over `D` is what makes the resolution
case compose: it lets us stack `C₁` then `C₂` before reasoning propositionally.
-/

/--
Adding a derived clause (over any clause context `D`) preserves `evalPrefix`.

The `Nodup` hypothesis is inherited from `evalPrefix_reduce` — and is genuinely needed:
`∀u ∃u. (u)` is true, yet `ax` followed by `red` "refutes" it (see the counterexamples
above), so soundness fails outright on prefixes with repeated binders.
-/
theorem QRes.inv {Φ : QBF} (hnd : (Prefix.vars Φ.pre).Nodup)
    {C : CNF.Clause Var} (h : QRes Φ C) :
    ∀ (σ : Assignment) (D : CNF Var),
      evalPrefix Φ.pre σ (Φ.matrix ++ D) → evalPrefix Φ.pre σ ((Φ.matrix ++ D).add C) := by
  induction h with
  | @ax C hmem hnt =>
      intro σ D hσ
      refine evalPrefix_mono Φ.pre (Φ.matrix ++ D) ((Φ.matrix ++ D).add C) ?_ σ hσ
      intro τ hτ
      rw [CNF.eval_add, Bool.and_eq_true]
      have hM : CNF.eval τ Φ.matrix = true := by
        rw [CNF.eval_append, Bool.and_eq_true] at hτ; exact hτ.1
      exact ⟨clause_eval_of_mem hmem hM, hτ⟩
  | @res C₁ C₂ x h₁ h₂ hx hx₁ hx₂ hnt ih₁ ih₂ =>
      intro σ D hσ
      have e1 : evalPrefix Φ.pre σ (Φ.matrix ++ D.add C₁) :=
        (evalPrefix_eval_congr Φ.pre σ ((Φ.matrix ++ D).add C₁) (Φ.matrix ++ D.add C₁)
          (fun τ => by
            simp only [CNF.eval_add, CNF.eval_append, Bool.and_assoc, Bool.and_comm,
              Bool.and_left_comm])).mp (ih₁ σ D hσ)
      have e2 : evalPrefix Φ.pre σ ((Φ.matrix ++ D.add C₁).add C₂) := ih₂ σ (D.add C₁) e1
      refine evalPrefix_mono Φ.pre _ ((Φ.matrix ++ D).add (resolvent C₁ C₂ x)) ?_ σ e2
      intro τ hτ
      simp only [CNF.eval_add, CNF.eval_append, Bool.and_eq_true] at hτ ⊢
      obtain ⟨hc2, hM, hc1, hD⟩ := hτ
      exact ⟨resolvent_sound h₁.not_taut h₂.not_taut hx₁ hx₂ hc1 hc2, hM, hD⟩
  | @red C u h hu hlvl ih =>
      intro σ D hσ
      exact evalPrefix_reduce h.not_taut Φ.pre hnd hu hlvl σ (Φ.matrix ++ D) (ih σ D hσ)

/-- Over a closed QBF, every derived clause mentions only prefix variables. -/
theorem QRes.mem_vars {Φ : QBF} (hcl : Φ.Closed) {C : CNF.Clause Var} (h : QRes Φ C) :
    ∀ v ∈ clauseVars C, v ∈ Prefix.vars Φ.pre := by
  induction h with
  | @ax C hmem _ =>
      intro v hv
      refine hcl v ?_
      rw [varMem_iff_mem_cnfVars]
      exact List.mem_flatMap.mpr ⟨C, Array.mem_def.mp hmem, hv⟩
  | @res C₁ C₂ x _ _ _ _ _ _ ih₁ ih₂ =>
      intro v hv
      obtain ⟨l, hl, rfl⟩ := mem_clauseVars.mp hv
      rcases List.mem_append.mp hl with hl | hl
      · exact ih₁ _ (mem_clauseVars.mpr ⟨l, (mem_eraseVar.mp hl).1, rfl⟩)
      · exact ih₂ _ (mem_clauseVars.mpr ⟨l, (mem_eraseVar.mp hl).1, rfl⟩)
  | @red C u _ _ _ ih =>
      intro v hv
      obtain ⟨l, hl, rfl⟩ := mem_clauseVars.mp hv
      exact ih _ (mem_clauseVars.mpr ⟨l, (mem_eraseVar.mp hl).1, rfl⟩)

/--
**Soundness.** A Q-resolution refutation certifies that the QBF is false — for a prefix
without repeated binders. (`Φ.WF.1` supplies the hypothesis for well-formed QBFs.)
-/
theorem QRes.sound {Φ : QBF} (hnd : (Prefix.vars Φ.pre).Nodup) (h : Φ.Refutes) :
    ¬ Φ.True := by
  intro htrue
  simp only [QBF.True] at htrue
  have key : evalPrefix Φ.pre (fun _ => false) (Φ.matrix ++ CNF.empty) :=
    (evalPrefix_eval_congr Φ.pre _ Φ.matrix (Φ.matrix ++ CNF.empty)
      (fun τ => by simp [CNF.eval_append])).mp htrue
  have hbad := QRes.inv hnd h (fun _ => false) CNF.empty key
  exact not_evalPrefix_of_unsat Φ.pre _ _ (fun τ => by simp [CNF.eval_add]) hbad

end Qbf
