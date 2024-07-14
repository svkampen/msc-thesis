import Mathlib.Tactic
import Thesis.ARS
import Mathlib.Logic.Relation

namespace Thesis

section reduction_seq

open Relation

variable {α I}
variable (A: ARS α I)

/--
`ReductionSeq A x y ss` represents a reduction sequence in `A`,
taking indexed reduction steps as given in `ss` from `x` to `y`.

An empty reduction sequence is represented by `ReductionSeq.refl`, allowing a
reduction from `x` to `x` in 0 steps. Using `ReductionSeq.head`, a single step
`a ⇒[i] b` can be prepended to an existing reduction sequence.
-/
inductive ReductionSeq: α → α → List (I × α) → Prop
  | refl {x} : ReductionSeq x x []
  | head {i x y} : A.rel i x y → ReductionSeq y z ss → ReductionSeq x z ((i, y)::ss)

def ReductionSeq.elems (hseq: ReductionSeq A x y ss) := x :: (ss.map (·.2))

theorem ReductionSeq.tail (hr: ReductionSeq A x y ss) (hstep: A.rel i y z) : ReductionSeq A x z (ss ++ [(i, z)]) := by
  induction hr with
  | refl => simp; apply head hstep; apply refl
  | head step r ih =>
    simp_all
    apply head step
    exact ih

theorem ReductionSeq.concat (h₁ : ReductionSeq A x y ss) (h₂: ReductionSeq A y z ss') : ReductionSeq A x z (ss ++ ss') := by
  induction h₁ with
  | refl => exact h₂
  | head hstep hseq ih =>
    apply head hstep (ih h₂)

/-- A reduction sequence exists iff there is a reflexive-transitive reduction. -/
lemma ReductionSeq.exists_iff_union_rel_star {x y : α}: A.union_rel∗ x y ↔ ∃ss, ReductionSeq A x y ss := by
  constructor <;> intro r
  · induction r using ReflTransGen.head_induction_on with
    | refl => use [], ReductionSeq.refl
    | head step seq ih =>
        obtain ⟨ss', hss'⟩ := ih
        obtain ⟨i, hi⟩ := step
        exact ⟨_, head hi hss'⟩
  · rcases r with ⟨ss, r⟩
    induction r with
    | refl => rfl
    | head step seq ih =>
      exact ReflTransGen.head ⟨_, step⟩ ih


end reduction_seq

end Thesis
