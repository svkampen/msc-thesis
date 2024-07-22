import Thesis.RelProps
import Thesis.Multiset

inductive Direction: Type where
| FW
| BW

def Rel.dir (r: Rel α α): Direction → (Rel α α)
| Direction.FW => r
| Direction.BW => r.inv

lemma Rel.dir_rev (r: Rel α α): r.dir Direction.FW x y ↔ r.dir Direction.BW y x := by
  constructor <;> (
    intro h
    simp [Rel.dir] at *
    assumption)

namespace Thesis
open Relation
open Classical

set_option linter.unusedVariables false

section SymmSeq

variable (r: Rel α α)

open Direction

abbrev Step (α: Type*) := (α × Direction × α)

abbrev Step.start (hs: Step α) := hs.1
abbrev Step.dir (hs: Step α) := hs.2.1
abbrev Step.end (hs: Step α) := hs.2.2

/-- A reduction sequence with forward and backward steps. -/
inductive SymmSeq: α → α → List (Step α) → Prop
| refl: SymmSeq x x []
| head (d: Direction) (hstep: (r.dir d) x y) (hseq: SymmSeq y z ss): SymmSeq x z ((x, d, y)::ss)

end SymmSeq

section SymmSeq.Lemmas

open SymmSeq
open Direction
open Classical

variable {r: Rel α α}

lemma SymmSeq.tail {x y z: α} (hseq: SymmSeq r x y ss) (hstep: (r.dir d) y z):
    SymmSeq r x z (ss ++ [(y, d, z)]) := by
  induction hseq with
  | refl =>
    apply head _ hstep refl
  | head d hstep' hseq' ih =>
    apply head _ hstep' (ih hstep)

lemma SymmSeq.symm {x y: α} (hseq: SymmSeq r x y ss): ∃ss', SymmSeq r y x ss' := by
  induction hseq with
  | refl => use [], refl
  | head d hstep hseq ih =>
    rename_i x' y' z' _
    cases d
    · obtain ⟨ss', hss'⟩ := ih
      use (ss' ++ [(y', BW, x')])
      rw [Rel.dir_rev] at hstep
      apply SymmSeq.tail hss' hstep
    · obtain ⟨ss', hss'⟩ := ih
      use (ss' ++ [(y', FW, x')])
      rw [<-Rel.dir_rev] at hstep
      apply SymmSeq.tail hss' hstep


lemma SymmSeq.concat {x y z: α} (h₁: SymmSeq r x y ss₁) (h₂: SymmSeq r y z ss₂): SymmSeq r x z (ss₁ ++ ss₂) := by
  induction h₁ with
  | refl => assumption
  | head d hstep hseq ih =>
    apply head _ hstep (ih h₂)

lemma SymmSeq.iff_conv {x y: α}: r⇔ x y ↔ ∃ss, SymmSeq r x y ss := by
  constructor
  · intro h; induction h with
    | rel x y _ => use [(x, FW, y)]; apply head _ _ refl; assumption
    | refl x => use [], refl
    | symm x y hr ih =>
      obtain ⟨ss, hss⟩ := ih
      apply hss.symm
    | trans x y z h₁ h₂ ih₁ ih₂ =>
      obtain ⟨ss₁, hss₁⟩ := ih₁
      obtain ⟨ss₂, hss₂⟩ := ih₂
      use (ss₁ ++ ss₂)
      apply SymmSeq.concat hss₁ hss₂
  · rintro ⟨ss, h⟩
    induction h with
    | refl => exact EqvGen.refl _
    | head d hstep hseq ih =>
      rename_i x' y' z' ss'
      apply EqvGen.trans x' y' z' _ ih
      cases d <;> simp [Rel.dir] at hstep
      pick_goal 2; apply EqvGen.symm; simp [Rel.inv, flip] at hstep
      all_goals { apply EqvGen.rel _ _ hstep }

lemma SymmSeq.if_rt: r∗ x y → ∃ss, SymmSeq r x y ss ∧ (∀s ∈ ss, s.dir = Direction.FW) := by
  intro h
  induction h using ReflTransGen.head_induction_on with
  | refl =>
    use [], SymmSeq.refl
    tauto
  | head step tail ih =>
    rename_i b c
    obtain ⟨ss', ⟨htail, h⟩⟩ := ih
    use ((b, Direction.FW, c)::ss')
    constructor
    · apply head
      · simp [Rel.dir]; exact step
      · exact htail
    · intro s
      intro hs
      aesop


-- A SymmSeq has a peak if there is a backward step followed by a forward step.
def SymmSeq.has_peak (hseq: SymmSeq r x y ss) := ∃n, ∃(h: n < ss.length - 1), ss[n].dir = BW ∧ ss[n+1].dir = FW

lemma SymmSeq.no_peak_cases (hseq: SymmSeq r x y ss) (hnp: ¬hseq.has_peak):
    (∀s ∈ ss, s.dir = Direction.FW) ∨ (∀s ∈ ss, s.dir = Direction.BW) ∨
    (∃ss₁ ss₂,
      ss = ss₁ ++ ss₂ ∧ ss₁ ≠ [] ∧ ss₂ ≠ [] ∧
      (∀s ∈ ss₁, s.dir = Direction.FW) ∧ (∀s ∈ ss₂, s.dir = Direction.BW) ∧
      (∃z, SymmSeq r x z ss₁ ∧ SymmSeq r z y ss₂)) := by
  induction hseq with
  | refl =>
    left; simp
  | head d hstep hseq ih =>
    have : ¬hseq.has_peak := by
      simp [has_peak] at hnp ⊢
      intro x hx
      have := hnp (x + 1) (by omega)
      simpa
    have ih' := ih this
    clear ih this
    cases hseq
    · cases d
      · left; simp
      · right; left; simp
    rcases ih' with h' | h' | h' <;>
      rename_i x y z y' ss' d' hstep' hseq'
    · cases d
      · left; simpa using h'
      · exfalso
        apply hnp
        use 0, (by simp)
        have := h' (y, d', y') (by simp)
        simpa
    · cases d
      · right; right
        use [(x, FW, y)], ((y, d', y')::ss')
        and_intros <;> try (simp; done)
        · exact h'
        · use y
          constructor
          · apply head _ hstep refl
          · apply head _ hstep' hseq'
      · right; left
        simp; constructor
        · have := h' (y, d', y') (by simp)
          simpa
        · intro x d y hdy
          have := h' (x, d, y) (by simp [hdy])
          simpa
    · right; right
      obtain ⟨ss₁, ss₂, heq, hne₁, hne₂, hfw, hbw, z', hseq₁, hseq₂⟩ := h'
      have hd: (d = Direction.FW)
      · by_contra
        have hd: d = BW := by cases d <;> tauto
        apply hnp
        use 0, (by simp), hd
        cases ss₁ with
        | nil => contradiction
        | cons head tail =>
          have: head.dir = FW := by simp [hfw]
          have: (y, d', y') = head := by simp at heq; tauto
          subst this
          simpa
      use ((x, d, y) :: ss₁), ss₂
      and_intros <;> try (simp_all; done)
      · use z'
        constructor
        apply head _ hstep hseq₁
        exact hseq₂


lemma SymmSeq.only_dir (hseq: SymmSeq r x y ss) (hss: ∀s ∈ ss, s.dir = d): (r.dir d)∗ x y := by
  induction hseq with
  | refl => rfl
  | head d' hstep hseq ih =>
    have hd: d = d' := by simp at hss; tauto
    subst hd
    refine ReflTransGen.head hstep (ih ?_)
    intro s a
    simp_all only [List.mem_cons, or_true, implies_true, true_implies, forall_eq_or_imp, Prod.forall, true_and]
    apply hss _ _ _ a


lemma SymmSeq.no_peak_congr (hseq: SymmSeq r x y ss) (hnp: ¬hseq.has_peak): ∃d, r∗ x d ∧ r∗ y d := by
  have := hseq.no_peak_cases hnp
  rcases this with h | h | ⟨l₁, l₂, -, -, -, hfw₁, hbw₂, hex⟩
  · use y
    exact ⟨hseq.only_dir h, by rfl⟩
  · use x
    exact ⟨by rfl, rel_inv_star.mp <| hseq.only_dir h⟩
  · obtain ⟨z, h₁, h₂⟩ := hex
    use z
    exact ⟨h₁.only_dir hfw₁, rel_inv_star.mp <| h₂.only_dir hbw₂⟩

lemma SymmSeq.get_step (hseq: SymmSeq r x y ss) (n: ℕ) (hn: n < ss.length):
    (r.dir ss[n].dir) ss[n].start ss[n].end := by
  induction hseq generalizing n with
  | refl =>
    contradiction
  | head d hstep hseq ih =>
    simp at hn
    cases n with
    | zero =>
      simp [Step.start, Step.end]
      exact hstep
    | succ n =>
      simp at hn
      simp
      apply ih n hn

def SymmSeq.elems (hseq: SymmSeq r x y ss): List α := (((x, FW, x)::ss).map (Step.end))

def SymmSeq.elems' (hseq: SymmSeq r x y ss): List α := ((ss.concat (y, FW, y)).map (Step.start))

lemma SymmSeq.elems_eq_elems' (hseq: SymmSeq r x y ss): hseq.elems = hseq.elems' := by
  induction hseq with
  | refl =>
    simp [elems, elems']
  | head d hstep hseq ih =>
    simp [elems, elems'] at ih ⊢
    simp [Step.end]
    exact ih

@[simp]
lemma SymmSeq.elems_length (hseq: SymmSeq r x y ss): hseq.elems.length = ss.length + 1 := by
  simp [elems]

lemma SymmSeq.take (hseq: SymmSeq r x y ss) (n: ℕ) (hn: n ≤ ss.length):
  SymmSeq r x (hseq.elems[n]'(by simp [elems]; omega)) (ss.take n) := by
  induction hseq generalizing n with
  | refl =>
    simp at hn
    subst hn
    simp; exact SymmSeq.refl
  | head d hstep hseq ih =>
    simp at hn
    cases n
    · simp; exact SymmSeq.refl
    · simp
      apply head _ hstep
      apply ih
      omega

lemma SymmSeq.drop (hseq: SymmSeq r x y ss) (n: ℕ) (hn: n ≤ ss.length):
  SymmSeq r (hseq.elems[n]'(by simp [elems]; omega)) y (ss.drop n) := by
  induction hseq generalizing n with
  | refl =>
    simp at hn
    subst hn
    simp; exact SymmSeq.refl
  | head d hstep hseq ih =>
    simp at hn
    cases n <;> simp
    · apply head _ hstep
      exact hseq
    · apply ih
      omega

lemma SymmSeq.step_start_end (hseq: SymmSeq r x y ss) (n: ℕ) (hn: n < ss.length - 1):
  ss[n].end = ss[n+1].start := by
  induction hseq generalizing n with
  | refl =>
    contradiction
  | head d hstep hseq ih =>
    cases hseq
    · contradiction
    cases n
    · simp
    · simp at ih ⊢
      apply ih
      simpa using hn

lemma SymmSeq.first_start (hseq: SymmSeq r x y ss) (hne: ss ≠ []):
    (ss[0]'(by exact List.length_pos.mpr hne)).start = x := by
  induction hseq with
  | refl => contradiction
  | head d hstep hseq ih =>
    simp

lemma SymmSeq.empty_eq: SymmSeq r x y [] → x = y := by
  intro hseq; cases hseq; rfl

lemma SymmSeq.last (hseq: SymmSeq r x y (ss' ++ [b])): b.end = y := by
  generalize hss: ss' ++ [b] = ss
  rw [hss] at hseq
  induction hseq generalizing ss' b with
  | refl => simp at hss
  | head d hstep hseq ih =>
    rename_i x y z ss
    cases ss' with
    | nil =>
      simp at hss
      rw [<-hss.2] at hseq
      cases hseq
      rw [hss.1]
    | cons head tail =>
      apply @ih tail
      simp_all


lemma SymmSeq.step_pred (hseq: SymmSeq r x y ss) (hs: s ∈ ss ∧ s.start ≠ x): ∃s' ∈ ss, s'.end = s.start := by
  induction hseq with
  | refl =>
    simp at hs
  | head d hstep hseq ih =>
    rename_i x y z ss
    simp at hs
    cases hs.1 with
    | inl h =>
      exfalso
      simp_all
    | inr h =>
      by_cases hy: (s.start = y)
      · use (x, d, y)
        simp [Step.end, hy]
      · obtain ⟨s', hss'⟩ := ih ⟨h, hy⟩
        use s'
        tauto


end SymmSeq.Lemmas

end Thesis
