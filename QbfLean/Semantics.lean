/-
# Semantics of quantified Boolean formulas

Two evaluators, and the basic metatheory connecting them:

* `Qbf.evalPrefix` — a `Prop`-valued semantics, defined by recursion on the prefix.
  This is the one you reason with: `∃` in the object language becomes `∃` in Lean.
* `Qbf.evalPrefixB` — a `Bool`-valued semantics that actually *runs* (naive
  quantifier expansion). This gives us `#eval` and the `decide` tactic on concrete
  instances.

Theorem `Qbf.evalPrefixB_eq_true` says the two agree, so we get the best of both.

The two payoff theorems at the end pin the definition down against what you already
know: a closed purely existential QBF is true iff its matrix is satisfiable, and a
closed purely universal one is true iff its matrix is valid.
-/

import QbfLean.Syntax

namespace Qbf

open Std.Sat

/-! ## Assignments -/

/--
A total assignment of truth values to variables.

We use *total* assignments (`Var → Bool`) rather than partial ones. This keeps the
semantics below clean — no "is this variable defined yet?" case analysis — at the cost
of having to state explicitly which variables a result actually depends on
(see `evalPrefix_congr`). Partial assignments become more natural once you get to
Skolem/Herbrand functions and certificate extraction, so expect to add a partial
variant plus a bridging lemma later.
-/
abbrev Assignment := Var → Bool

/--
`Assignment.set σ x b` is `σ` overwritten to send `x` to `b`.

NOTE: functions in Lean are values, so "updating" `σ` means building a new function.
`fun y => ...` is a lambda; `if y = x then _ else _` needs `DecidableEq Var`, which
`Var = Nat` has.
-/
def Assignment.set (σ : Assignment) (x : Var) (b : Bool) : Assignment :=
  fun y => if y = x then b else σ y

/--
Notation `σ[x ↦ b]` for `Assignment.set σ x b`.

NOTE: `syntax:max` declares new syntax at maximum precedence, so it binds tighter than
anything else and needs no extra parentheses; `macro_rules` says what it expands to.
`noWs` forbids whitespace before `[`, exactly like Lean's own `xs[i]` indexing. Without
it, the parser would read `f xs []` or `f xs [1]` as the start of `xs[_ ↦ _]` and fail.
It is `scoped`, so it is only available inside `namespace Qbf` or after `open Qbf`.
-/
scoped syntax:max term noWs "[" term " ↦ " term "]" : term

scoped macro_rules
  | `($σ[$x ↦ $b]) => `(Assignment.set $σ $x $b)

/-- Pretty-print `Assignment.set σ x b` back as `σ[x ↦ b]` in goals. -/
@[scoped app_unexpander Assignment.set]
def unexpandAssignmentSet : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $x $b) => `($σ[$x ↦ $b])
  | _ => throw ()

-- Regression check: a list literal after an application argument is not mistaken for
-- the start of `σ[x ↦ b]`.
example (xs : List Nat) : List.append xs [] = xs ∧ List.append xs [1] = xs ++ [1] :=
  ⟨List.append_nil xs, rfl⟩

@[simp] theorem Assignment.set_same (σ : Assignment) (x : Var) (b : Bool) :
    σ[x ↦ b] x = b := by
  simp [Assignment.set]

@[simp] theorem Assignment.set_other {x y : Var} (σ : Assignment) (b : Bool) (h : y ≠ x) :
    σ[x ↦ b] y = σ y := by
  simp [Assignment.set, h]

/-! ## The semantics -/

/--
`evalPrefix p σ φ` holds when the QBF with prefix `p` and matrix `φ` is true under the
assignment `σ` to the variables *not* bound by `p`.

NOTE: this is defined by structural recursion on the prefix. Read the three cases as:
* empty prefix — just evaluate the CNF matrix under `σ`;
* `∃x` — *some* Boolean value for `x` makes the rest true;
* `∀x` — *every* Boolean value for `x` makes the rest true.

NOTE: the result is a `Prop`, and the `∃`/`∀` on the right-hand sides are Lean's own
quantifiers. This is what makes the definition pleasant to reason about: object-level
quantifier reasoning turns into ordinary Lean quantifier reasoning. It is *not*
executable, though — hence `evalPrefixB` below.
-/
def evalPrefix : Prefix → Assignment → CNF Var → Prop
  | [],             σ, φ => CNF.eval σ φ = true
  | (.ex,  x) :: p, σ, φ => ∃ b : Bool, evalPrefix p σ[x ↦ b] φ
  | (.all, x) :: p, σ, φ => ∀ b : Bool, evalPrefix p σ[x ↦ b] φ

/-
NOTE: each of these holds by definition (`Iff.rfl` = "both sides are literally the
same proposition"), but stating them as `@[simp]` lemmas lets `simp` unfold the
recursion one step at a time, which is much better behaved than unfolding `evalPrefix`
wholesale.
-/
@[simp] theorem evalPrefix_nil (σ : Assignment) (φ : CNF Var) :
    evalPrefix [] σ φ ↔ CNF.eval σ φ = true := Iff.rfl

@[simp] theorem evalPrefix_ex (x : Var) (p : Prefix) (σ : Assignment) (φ : CNF Var) :
    evalPrefix ((Quant.ex, x) :: p) σ φ ↔ ∃ b : Bool, evalPrefix p σ[x ↦ b] φ := Iff.rfl

@[simp] theorem evalPrefix_all (x : Var) (p : Prefix) (σ : Assignment) (φ : CNF Var) :
    evalPrefix ((Quant.all, x) :: p) σ φ ↔ ∀ b : Bool, evalPrefix p σ[x ↦ b] φ := Iff.rfl

/--
Truth of a (closed) QBF. The starting assignment is irrelevant for closed QBFs — that
is exactly `QBF.true_congr` below — so we pick the all-false one.
-/
def QBF.True (Φ : QBF) : Prop := evalPrefix Φ.pre (fun _ => false) Φ.matrix

/-! ## An executable evaluator -/

/--
Naive Bool-valued evaluation: expand each quantifier into the two branches `x ↦ false`
and `x ↦ true`. Exponential in the number of variables, obviously — this is for
`#eval`, sanity checks and small unit tests, not for solving.
-/
def evalPrefixB : Prefix → Assignment → CNF Var → Bool
  | [],             σ, φ => CNF.eval σ φ
  | (.ex,  x) :: p, σ, φ => evalPrefixB p σ[x ↦ false] φ || evalPrefixB p σ[x ↦ true] φ
  | (.all, x) :: p, σ, φ => evalPrefixB p σ[x ↦ false] φ && evalPrefixB p σ[x ↦ true] φ

/--
The computable and the logical semantics agree.

NOTE: `induction p generalizing σ` is the key move. The recursive calls in `evalPrefix`
happen at a *different* assignment (`σ[x ↦ b]`, not `σ`), so the induction hypothesis
has to be available for all assignments, not just the current one. Forgetting
`generalizing` is one of the most common ways an induction gets stuck in Lean.
-/
theorem evalPrefixB_eq_true (p : Prefix) (σ : Assignment) (φ : CNF Var) :
    evalPrefixB p σ φ = true ↔ evalPrefix p σ φ := by
  induction p generalizing σ with
  | nil => simp [evalPrefixB]
  | cons qx p ih =>
    -- `obtain ⟨q, x⟩ := qx` splits the pair; `cases q` splits into the ∃ and ∀ cases.
    obtain ⟨q, x⟩ := qx
    cases q with
    | ex =>
      simp only [evalPrefixB, evalPrefix_ex, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · exact ⟨false, (ih _).mp h⟩
        · exact ⟨true, (ih _).mp h⟩
      · rintro ⟨b, hb⟩
        cases b
        · exact Or.inl ((ih _).mpr hb)
        · exact Or.inr ((ih _).mpr hb)
    | all =>
      simp only [evalPrefixB, evalPrefix_all, Bool.and_eq_true]
      constructor
      · rintro ⟨h₀, h₁⟩ b
        cases b
        · exact (ih _).mp h₀
        · exact (ih _).mp h₁
      · intro h
        exact ⟨(ih _).mpr (h false), (ih _).mpr (h true)⟩

/--
Truth of a QBF is decidable — by brute force, via `evalPrefixB`.

NOTE: an `instance` is a value the typeclass resolver finds automatically. Registering
this one is what makes `by decide` work on concrete QBFs, and it is why
`if evalPrefix p σ φ then _ else _` would typecheck. `decidable_of_iff` transports
decidability of `evalPrefixB p σ φ = true` (which is just `Bool` equality) across the
theorem above.
-/
instance instDecidableEvalPrefix (p : Prefix) (σ : Assignment) (φ : CNF Var) :
    Decidable (evalPrefix p σ φ) :=
  decidable_of_iff _ (evalPrefixB_eq_true p σ φ)

instance instDecidableQBFTrue (Φ : QBF) : Decidable Φ.True :=
  instDecidableEvalPrefix _ _ _

/-! ## Truth only depends on the free variables -/

/--
Assignments that agree on every matrix variable *not* bound by the prefix give the same
truth value. This is the QBF analogue of the standard "coincidence lemma".

NOTE: the proof is the archetypal induction over a binder structure. In the `cons` case
we must re-establish the agreement hypothesis for the *updated* assignments: on the
newly bound variable `x` both sides are `b`, and elsewhere we fall back to the original
hypothesis.
-/
theorem evalPrefix_congr (p : Prefix) (φ : CNF Var) (σ₁ σ₂ : Assignment)
    (h : ∀ v, CNF.VarMem v φ → v ∉ Prefix.vars p → σ₁ v = σ₂ v) :
    evalPrefix p σ₁ φ ↔ evalPrefix p σ₂ φ := by
  induction p generalizing σ₁ σ₂ with
  | nil =>
    -- No bound variables, so `σ₁` and `σ₂` agree on *all* variables of `φ`.
    simp only [evalPrefix_nil]
    rw [CNF.eval_congr σ₁ σ₂ φ fun v hv => h v hv (by simp)]
  | cons qx p ih =>
    obtain ⟨q, x⟩ := qx
    -- The updated assignments still satisfy the agreement hypothesis, one binder in.
    have hstep : ∀ b : Bool, ∀ v, CNF.VarMem v φ → v ∉ Prefix.vars p →
        σ₁[x ↦ b] v = σ₂[x ↦ b] v := by
      intro b v hv hnv
      by_cases hvx : v = x
      · subst hvx; simp
      · rw [Assignment.set_other _ _ hvx, Assignment.set_other _ _ hvx]
        exact h v hv (by simp [hvx, hnv])
    cases q with
    | ex =>
      simp only [evalPrefix_ex]
      exact exists_congr fun b => ih _ _ (hstep b)
    | all =>
      simp only [evalPrefix_all]
      exact forall_congr' fun b => ih _ _ (hstep b)

/-- For a closed QBF the initial assignment is irrelevant. -/
theorem QBF.true_congr {Φ : QBF} (hcl : Φ.Closed) (σ : Assignment) :
    evalPrefix Φ.pre σ Φ.matrix ↔ Φ.True :=
  evalPrefix_congr _ _ _ _ fun v hv hnv => absurd (hcl v hv) hnv

/-! ## Sanity checks: the purely existential and purely universal fragments -/

/--
A purely existential prefix is exactly an existential quantification over assignments
to the prefix variables.

NOTE: `hp : ∀ qx ∈ p, qx.1 = Quant.ex` says every entry of the prefix is existential.
`∀ x ∈ l, P x` is sugar for `∀ x, x ∈ l → P x`.
-/
theorem evalPrefix_of_allEx (p : Prefix) (hp : ∀ qx ∈ p, qx.1 = Quant.ex)
    (σ : Assignment) (φ : CNF Var) :
    evalPrefix p σ φ ↔
      ∃ τ : Assignment, (∀ v, v ∉ Prefix.vars p → τ v = σ v) ∧ CNF.eval τ φ = true := by
  induction p generalizing σ with
  | nil =>
    simp only [evalPrefix_nil, Prefix.vars_nil]
    constructor
    · intro h; exact ⟨σ, fun _ _ => rfl, h⟩
    · rintro ⟨τ, hτ, h⟩
      have : τ = σ := funext fun v => hτ v (by simp)
      subst this; exact h
  | cons qx p ih =>
    obtain ⟨q, x⟩ := qx
    -- The head quantifier is existential, by `hp`.
    obtain rfl : q = Quant.ex := hp (q, x) (List.mem_cons_self ..)
    have hp' : ∀ qx ∈ p, qx.1 = Quant.ex := fun qx hqx => hp qx (List.mem_cons_of_mem _ hqx)
    simp only [evalPrefix_ex, Prefix.vars_cons, List.mem_cons, not_or]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨τ, hτ, hev⟩ := (ih hp' _).mp hb
      refine ⟨τ, fun v hv => ?_, hev⟩
      rw [hτ v hv.2, Assignment.set_other _ _ hv.1]
    · rintro ⟨τ, hτ, hev⟩
      -- Pick the witness for `x` that `τ` itself uses.
      refine ⟨τ x, (ih hp' _).mpr ⟨τ, fun v hv => ?_, hev⟩⟩
      by_cases hvx : v = x
      · subst hvx; simp
      · rw [Assignment.set_other _ _ hvx]
        exact hτ v ⟨hvx, hv⟩

/--
**A closed purely existential QBF is true iff its matrix is satisfiable.**

This is the sanity check that our prefix semantics really does generalise SAT.
`CNF.Sat τ φ` is core's `CNF.eval τ φ = true`.
-/
theorem QBF.true_iff_sat (Φ : QBF) (hcl : Φ.Closed) (hp : ∀ qx ∈ Φ.pre, qx.1 = Quant.ex) :
    Φ.True ↔ ∃ τ : Assignment, CNF.Sat τ Φ.matrix := by
  rw [QBF.True, evalPrefix_of_allEx _ hp]
  constructor
  · rintro ⟨τ, _, hev⟩; exact ⟨τ, hev⟩
  · rintro ⟨τ, hev⟩
    -- Patch `τ` outside the prefix variables so that it agrees with the initial
    -- assignment there; by closedness this does not change the value of the matrix.
    refine ⟨fun v => if v ∈ Prefix.vars Φ.pre then τ v else false, fun v hv => by simp [hv], ?_⟩
    rw [← CNF.eval_congr τ _ Φ.matrix fun v hv => by simp [hcl v hv]]
    exact hev

/--
Dually: a closed purely universal QBF is true iff its matrix is valid.
-/
theorem QBF.true_iff_valid (Φ : QBF) (hcl : Φ.Closed) (hp : ∀ qx ∈ Φ.pre, qx.1 = Quant.all) :
    Φ.True ↔ ∀ τ : Assignment, CNF.Sat τ Φ.matrix := by
  have key : ∀ (p : Prefix), (∀ qx ∈ p, qx.1 = Quant.all) → ∀ (σ : Assignment),
      evalPrefix p σ Φ.matrix ↔
        ∀ τ : Assignment, (∀ v, v ∉ Prefix.vars p → τ v = σ v) → CNF.eval τ Φ.matrix = true := by
    intro p
    induction p with
    | nil =>
      intro _ σ
      simp only [evalPrefix_nil, Prefix.vars_nil]
      constructor
      · intro h τ hτ
        have : τ = σ := funext fun v => hτ v (by simp)
        subst this; exact h
      · intro h; exact h σ fun _ _ => rfl
    | cons qx p ih =>
      obtain ⟨q, x⟩ := qx
      intro hp σ
      obtain rfl : q = Quant.all := hp (q, x) (List.mem_cons_self ..)
      have hp' : ∀ qx ∈ p, qx.1 = Quant.all := fun qx hqx => hp qx (List.mem_cons_of_mem _ hqx)
      simp only [evalPrefix_all, Prefix.vars_cons, List.mem_cons, not_or]
      constructor
      · intro h τ hτ
        refine (ih hp' σ[x ↦ τ x]).mp (h (τ x)) τ fun v hv => ?_
        by_cases hvx : v = x
        · subst hvx; simp
        · rw [Assignment.set_other _ _ hvx]; exact hτ v ⟨hvx, hv⟩
      · intro h b
        refine (ih hp' σ[x ↦ b]).mpr fun τ hτ => h τ fun v hv => ?_
        rw [hτ v hv.2, Assignment.set_other _ _ hv.1]
  rw [QBF.True, key _ hp]
  constructor
  · intro h τ
    -- Patch `τ` outside the prefix variables, as above.
    have := h (fun v => if v ∈ Prefix.vars Φ.pre then τ v else false) (fun v hv => by simp [hv])
    -- NOTE: `show` restates the goal in a definitionally equal form; `CNF.Sat τ φ` is
    -- by definition `CNF.eval τ φ = true`, and `rw` needs to see the latter.
    show CNF.eval τ Φ.matrix = true
    rw [CNF.eval_congr τ (fun v => if v ∈ Prefix.vars Φ.pre then τ v else false) Φ.matrix
      fun v hv => by simp [hcl v hv]]
    exact this
  · intro h τ _; exact h τ

/-
## Where to go next

* **Negation.** `¬Φ` is *not* expressible inside this type: dualising the prefix
  (`Prefix.dual`) is easy, but negating a CNF matrix leaves CNF. Either add a general
  formula type with a Tseitin transformation to CNF, or state the duality theorem in
  the mixed form `¬ evalPrefix p σ φ ↔ evalPrefix (Prefix.dual p) σ (negate φ)` for a
  `negate` producing a DNF/AIG.

-/

end Qbf
