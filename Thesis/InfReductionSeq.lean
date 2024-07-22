import Mathlib.Tactic
import Mathlib.Logic.Relation

namespace Thesis.InfReductionSeq

section inf_reduction_seq

open Relation Classical

postfix:max (priority := high) "∗" => ReflTransGen
postfix:max (priority := high) "⁺" => TransGen

variable {α}

section irs_def

variable (r: Rel α α)

def is_inf_reduction_seq (f: ℕ → α) :=
  ∀n, r (f n) (f (n + 1))

end irs_def

variable {r: Rel α α}

/-- A transitive step can be decomposed into a step and, potentially, a remaining transitive step. -/
lemma internal_step: r⁺ a b → ∃c, r a c ∧ (c = b ∨ r⁺ c b) := by
  intro hr
  induction hr using TransGen.head_induction_on with
  | base h => use b, h; left; rfl
  | ih h₁ h₂ _ih =>
    rename_i a c
    use c, h₁; right; exact h₂

/-- Given an infinite sequence of transitive steps, there is always a next small step. -/
lemma step (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f) (a: α): (∃n, r⁺ a (f n)) → (∃(p: ℕ × α), r a p.2 ∧ r⁺ p.2 (f p.1)) := by
  rintro ⟨n, hr⟩
  obtain ⟨c, hc⟩ := internal_step hr
  cases hc.right with
  | inl h =>
    use (n + 1, c), hc.left
    simp [h, hf n]
  | inr h =>
    use (n, c)
    tauto

/--
A transitive infinite reduction sequence can be turned into
a regular infinite reduction sequence.
-/
lemma of_trans (f: ℕ → α) (hf: is_inf_reduction_seq r⁺ f): ∃f', is_inf_reduction_seq r f' := by
  have hstep := step f hf

  let f': α → α :=
    fun x ↦ if h: ∃n, r⁺ x (f n) then (choose (hstep x h)).2 else x

  have h₁ : ∀a, (∃n, r⁺ a (f n)) → (∃n, r⁺ (f' a) (f n)) := by
    rintro a h
    have := choose_spec (hstep a h)
    simp [f', dif_pos h]
    obtain ⟨-, right⟩ := this
    exact Exists.intro (choose (hstep a h)).1 right

  have h₂ : ∀a, (∃n, r⁺ a (f n)) → r a (f' a) := by
    intro a h
    have := choose_spec (hstep a h)
    simp [f', dif_pos h]
    tauto

  have: ∀N, ∃n, r⁺ (f'^[N] (f 0)) (f n) := Function.Iterate.rec _ h₁ ⟨1, hf 0⟩

  use (f'^[·] (f 0))
  simp only [is_inf_reduction_seq]
  intro n
  rw [Function.iterate_succ', Function.comp]
  exact h₂ (f'^[n] (f 0)) (this n)


-- The above is still not as strong as ReductionSeq.flatten, and only
-- flattens a transitive reduction sequence.

-- Building an `of_refl_trans` is even more complicated, and if the
-- reflexive-transitive seq has a point beyond which all steps are reflexive,
-- the 'flattened' version would be finite, so there really need to be two
-- separate defs which produce either version depending on the sequence.
-- lemma of_refl_trans (f: ℕ → α) (hf: is_inf_reduction_seq r∗ f): ???

end inf_reduction_seq

end Thesis.InfReductionSeq
