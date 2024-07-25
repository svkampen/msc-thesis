import Mathlib.Tactic
import Mathlib.Logic.Relation
import Thesis.RelProps

namespace Thesis

section reduction_seq

open Relation

variable {α}

section rs_def

variable (r: Rel α α)

structure RSStep (α: Type*) where
  start: α
  stop: α

/--
`ReductionSeq r x y ss` represents a reduction sequence, taking
reduction steps as given in `ss` from `x` to `y`.

An empty reduction sequence is represented by `ReductionSeq.refl`, allowing a
reduction from `x` to `x` in 0 steps. Using `ReductionSeq.head`, a single step
`r a b` can be prepended to an existing reduction sequence.
-/
inductive ReductionSeq: α → α → List (RSStep α) → Prop
  | refl {x} : ReductionSeq x x []
  | head {x y z ss} : r x y → ReductionSeq y z ss → ReductionSeq x z (⟨x, y⟩::ss)

end rs_def

variable {r: Rel α α}

namespace ReductionSeq

def elems (_: ReductionSeq r x y ss) := x :: (ss.map RSStep.stop)

lemma y_elem (hseq: ReductionSeq r x y ss): y ∈ hseq.elems := by
  induction hseq with
  | refl => simp [elems]
  | @head x y z ss step seq ih =>
    simp [elems] at ih ⊢
    tauto

lemma tail (hr: ReductionSeq r x y ss) (hstep: r y z): ReductionSeq r x z (ss ++ [⟨y, z⟩]) := by
  induction hr with
  | refl => simp; apply head hstep; apply refl
  | head step r ih =>
    simp_all
    apply head step
    exact ih

lemma concat (h₁ : ReductionSeq r x y ss) (h₂: ReductionSeq r y z ss'): ReductionSeq r x z (ss ++ ss') := by
  induction h₁ with
  | refl => exact h₂
  | head hstep _ ih =>
    apply head hstep (ih h₂)

/--
If `a` is an element of a concatenated sequence, it must be a member of one of
the two subsequences.
-/
lemma mem_concat (hseq₁: ReductionSeq r x y ss₁) (hseq₂: ReductionSeq r y z ss₂):
    ∀x, x ∈ (hseq₁.concat hseq₂).elems ↔ (x ∈ hseq₁.elems ∨ x ∈ hseq₂.elems) := by
  intro a
  induction hseq₁ with
  | refl => simp [concat, elems]
  | @head x y z ss step seq ih =>
    simp [concat]
    have ih := ih hseq₂
    have := seq.y_elem
    simp [elems] at this ih ⊢
    clear * -ih this
    aesop


/-- A reduction sequence exists iff there is a reflexive-transitive reduction step. -/
lemma exists_iff_rel_star {x y : α}: r∗ x y ↔ ∃ss, ReductionSeq r x y ss := by
  constructor <;> intro r
  · induction r using ReflTransGen.head_induction_on with
    | refl => use [], refl
    | head step seq ih =>
        obtain ⟨ss', hss'⟩ := ih
        exact ⟨_, head step hss'⟩
  · rcases r with ⟨ss, r⟩
    induction r with
    | refl => rfl
    | head step seq ih =>
      exact ReflTransGen.head step ih


lemma to_reduction_seq (hseq: ReductionSeq r x y ss):
    ∃(N :ℕ), ∃f, reduction_seq r N f ∧ (∀x ∈ hseq.elems, ∃n ≤ N, f n = x) ∧ f 0 = x := by
  induction hseq with
  | @refl x =>
    use 0, Function.const _ x
    constructor
    · simp [reduction_seq]
    · simp [elems]
  | @head x y z ss hstep hseq ih =>
    obtain ⟨N, f, hrs, hmem, hstart⟩ := ih
    use (N + 1)
    use (fun n ↦ if n = 0 then x else f (n - 1))
    and_intros
    · simp [reduction_seq]
      intro n hn
      cases n with
      | zero => rw [hstart]; simp; exact hstep
      | succ n =>
        norm_cast at hn
        simp at hn ⊢
        apply hrs
        norm_cast
    · simp [elems]
      and_intros
      · use 0; simp
      · use 1; simp [hstart]
      · simp [elems] at hmem
        intro a ha
        obtain ⟨n, hn⟩ := hmem.2 a ha
        use (n + 1)
        simpa
    · simp



lemma of_reduction_seq (N: ℕ) (f: ℕ → α) (hrs: reduction_seq r N f):
    ∃ss, ∃(hseq: ReductionSeq r (f 0) (f N) ss), ∀n ≤ N, f n ∈ hseq.elems := by
  induction N with
  | zero =>
    use [], refl
    simp [elems]
  | succ n ih =>
    have hrs': reduction_seq r n f := by
      intro n hn
      apply hrs
      norm_cast at *
      omega
    obtain ⟨ss', hseq', hss'⟩ := ih hrs'
    have hstep: r (f n) (f (n + 1)) := by
      apply hrs
      norm_cast
      norm_num
    use ss' ++ [⟨f n, f (n + 1)⟩]
    use tail hseq' hstep
    intro n' hn'
    rw [Nat.le_succ_iff] at hn'
    rcases hn' with (hn' | hn')
    · simp [elems] at hss' ⊢
      have := hss' n' hn'
      itauto
    · simp [elems]
      rw [hn', Nat.succ_eq_add_one]
      tauto


/--
A reflexive-transitive reduction sequence `a₀ ->* a₁ ->* ... ->* aₙ` can be
'flattened' (by analogy to a nested list) to a regular reduction sequence
`a₀ -> ... -> a₁ -> ... -> aₙ` which contains all elements of the original
sequence.
-/
lemma flatten (hseq: ReductionSeq r∗ x y ss):
    ∃ss', ∃(hseq': ReductionSeq r x y ss'), ∀a ∈ hseq.elems, a ∈ hseq'.elems := by
  induction hseq with
  | refl =>
    use [], refl
    simp [elems]
  | @head x y z ss hstep htail ih =>
    obtain ⟨ss₁, hseq₁⟩ := exists_iff_rel_star.mp hstep
    obtain ⟨ss₂, hseq₂, hmem⟩ := ih
    use (ss₁ ++ ss₂), hseq₁.concat hseq₂
    simp [mem_concat hseq₁ hseq₂]
    intro a ha
    simp only [elems, List.map_cons, List.mem_cons] at ha ⊢
    rcases ha with (rfl | rfl | ha) <;> try tauto
    · have := hmem a (by simp [elems] at ha ⊢; tauto)
      simp only [elems, List.mem_cons] at this
      right; assumption

end ReductionSeq

end reduction_seq

end Thesis
