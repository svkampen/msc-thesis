import Mathlib.Tactic
import Thesis.ARS
import Mathlib.Logic.Relation

namespace Thesis

section reduction_seq

open Relation

variable {α I}
variable (A: ARS α I)

/--
`ReductionSeq A is x y` represents a reduction sequence in `A`,
taking indexed reduction steps as given in `is` from `x` to `y`.

An empty reduction sequence is represented by `ReductionSeq.refl`, allowing a
reduction from `x` to `x` in 0 steps. Using `ReductionSeq.head`, a single step
`a ⇒[i] b` can be prepended to an existing reduction sequence.
-/
inductive ReductionSeq: List I → α → α → Prop
  | refl (x) : ReductionSeq [] x x
  | head {i x y z} : A.rel i x y → ReductionSeq is y z → ReductionSeq (i :: is) x z

theorem ReductionSeq.tail (hr : ReductionSeq A l a b) (hstep : A.rel i b c) : ReductionSeq A (l ++ [i]) a c := by
  induction hr with
  | refl => apply head hstep; exact refl c
  | head step _ ih => exact head step (ih hstep)

theorem ReductionSeq.concat : ReductionSeq A l x y → ReductionSeq A l' y z → ReductionSeq A (l ++ l') x z := by
  intro r₁ r₂
  induction r₁ with
  | refl a => rwa [List.nil_append]
  | head step _ ih => exact ReductionSeq.head step (ih r₂)

/-- A reduction sequence exists iff there is a reflexive-transitive reduction. -/
lemma ReductionSeq.exists_iff_union_rel_star {x y : α} : A.union_rel_star x y ↔ ∃is, ReductionSeq A is x y := by
  constructor <;> intro r
  · induction r using ReflTransGen.head_induction_on with
    | refl => use []; exact ReductionSeq.refl y
    | head step _ ih =>
        obtain ⟨is, h⟩ := ih
        obtain ⟨i, h'⟩ := step
        use (i :: is)
        apply ReductionSeq.head h' h
  · rcases r with ⟨is, r⟩
    induction r with
    | refl a => apply ReflTransGen.refl
    | head step _ ih =>
        apply ReflTransGen.head
        · exact Exists.intro _ step
        · exact ih


def ReductionSeq.labels : ReductionSeq A l x y → List I :=
  fun _ ↦ l

end reduction_seq

end Thesis
