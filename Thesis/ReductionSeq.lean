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
lemma ReductionSeq.exists_iff_union_rel_star {x y : α} : A.union_rel∗ x y ↔ ∃is, ReductionSeq A is x y := by
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


/-- A more complicated version of ReductionSeq that includes all of the elements. -/
inductive ReductionSeq': List I → List α → α → α → Prop
  | rel {i x y} : A.rel i x y → ReductionSeq' [i] [x, y] x y
  | head {i x y z} : A.rel i x y → ReductionSeq' is as y z → ReductionSeq' (i::is) (x::as) x z

theorem ReductionSeq'.tail (hr: ReductionSeq' A is as x y) (hstep: A.rel i y z) : ReductionSeq' A (is ++ [i]) (as ++ [z]) x z := by
  induction hr with
  | rel hr => apply head hr; exact rel hstep
  | head step _ ih => apply head step; apply ih; simp_all only [List.cons_append, List.getLast?_cons_cons]

theorem ReductionSeq'.concat (h₁ : ReductionSeq' A is as x y) (h₂: ReductionSeq' A is' (y::as') y z) : ReductionSeq' A (is ++ is') (as ++ as') x z := by
  induction h₁ with
  | rel hr => apply head hr; exact h₂
  | head step _ ih => apply head step (ih h₂)

lemma ReductionSeq'.as_last : ReductionSeq' A is as x y → ∃as', as = (as' ++ [y]) := by
  intro hr
  induction hr with
  | rel h => rename_i i x y; use [x]; rfl
  | head h h' ih => rename_i is as i x y z; obtain ⟨as', has'⟩ := ih; use (x::as'); simp_all only [List.cons_append]

lemma ReductionSeq'.as_head : ReductionSeq' A is as x y → ∃as', as = (x::as') := by
  intro hr; cases hr; use [y]; simp

/-- A reduction sequence exists iff there is a nonempty reflexive-transitive reduction. -/
lemma ReductionSeq'.exists_iff_union_rel_star {x y : α} (hne: x ≠ y): A.union_rel∗ x y ↔ ∃is as, ReductionSeq' A is as x y := by
  constructor <;> intro r
  · induction r using ReflTransGen.head_induction_on with
    | refl => contradiction
    | head step _ ih =>
        rename_i a c h
        obtain ⟨i, h'⟩ := step
        by_cases hc: (c = y)
        · rw [<-hc]
          use [i], [a, c]; exact rel h'
        · simp [hc] at ih
          obtain ⟨is, ⟨as, h⟩⟩ := ih
          use (i :: is), (a :: as)
          apply head h' h
  · rcases r with ⟨is, as, r⟩
    clear hne
    induction r with
    | rel a => rename_i i x y; apply ReflTransGen.single; use i
    | head step h ih =>
        rename_i is as i x y z
        apply ReflTransGen.head
        · exact Exists.intro _ step
        · exact ih


end reduction_seq

end Thesis
