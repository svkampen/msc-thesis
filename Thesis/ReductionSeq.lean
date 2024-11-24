import Mathlib.Tactic
import Mathlib.Logic.Relation
import Thesis.Misc

namespace Thesis

open Relation

variable {α}

section functional_def

variable (r: Rel α α)

/--
A generic reduction sequence, which is finite if `N ≠ ⊤` and infinite otherwise.
-/
abbrev reduction_seq (N: ℕ∞) (f: ℕ → α) :=
  ∀n: ℕ, n < N → r (f n) (f (n + 1))

def reduction_seq_rtg (N: ℕ∞) (f: ℕ → α) :=
  ∀(n : ℕ), (h: n < N) → r∗ (f n) (f (n + 1))

@[simp]
lemma reduction_seq_top_iff: reduction_seq r ⊤ f ↔ ∀n, r (f n) (f (n + 1)) := by
  simp [reduction_seq]

@[simp↓]
lemma reduction_seq_coe_iff {N: ℕ}: reduction_seq r N f ↔ ∀n < N, r (f n) (f (n + 1)) := by
  simp [reduction_seq]

/-- In an infinite reduction sequence, we can take a step from any `n` to `n + 1`. -/
lemma reduction_seq.inf_step {r: Rel α α} (hseq: reduction_seq r ⊤ f) (n: ℕ): r (f n) (f (n + 1)) := by
  simpa using hseq n

/-- Any function is a length-0 reduction sequence, containing only f 0. -/
lemma reduction_seq.refl (f: ℕ → α): reduction_seq r 0 f := by
  simp [reduction_seq]


lemma reduction_seq.from_reflTrans {r: Rel α α} (hrt: r∗ a b): ∃(N: ℕ) (f: ℕ → α), reduction_seq r N f ∧ f 0 = a ∧ f N = b := by
  induction hrt with
  | refl => use 0, (fun _ ↦ a), reduction_seq.refl _ _
  | @tail b c seq step ih =>
    obtain ⟨N, f, seq, hstart, hend⟩ := ih
    let f': ℕ → α := fun m ↦ if (m < N + 1) then (f m) else c
    use N + 1, f'
    simp +contextual [f', hstart] at seq ⊢
    intro n hn
    split
    case isTrue h => simpa using seq n h
    case isFalse h =>
      have: n = N := by omega
      simp_all only [lt_add_iff_pos_right, zero_lt_one, lt_self_iff_false, not_false_eq_true]


/--
In a generic reduction sequence `reduction_seq r N f`,
`f m` is a reduct of `f n`, assuming `n < m < N + 1`.
-/
lemma reduction_seq.trans {r: Rel α α} (hseq: reduction_seq r N f) (n m: ℕ) (hm: m < N + 1) (hn: n < m): r⁺ (f n) (f m) := by
  obtain ⟨k, hk⟩: ∃k, m = n + k + 1 := Nat.exists_eq_add_of_lt (by omega)
  subst hk
  induction k with
  | zero =>
    refine TransGen.single (hseq _ ?_)
    norm_num at hm
    exact lt_of_add_lt_add_right hm
  | succ k ih =>
    apply TransGen.tail
    · apply ih
      trans ((n + k + 1) + 1).cast
      · norm_cast; linarith
      · exact hm
      linarith
    apply hseq
    norm_num at hm ⊢
    exact lt_of_add_lt_add_right hm


lemma reduction_seq.reflTrans {r: Rel α α} (hseq: reduction_seq r N f) (n m: ℕ) (hm: m < N + 1) (hn: n ≤ m): r∗ (f n) (f m) := by
  rcases (Nat.eq_or_lt_of_le hn) with (rfl | hn)
  · rfl
  · apply TransGen.to_reflTransGen
    apply reduction_seq.trans hseq n m hm hn


@[simp]
def reduction_seq.elems (hseq: reduction_seq r N f): Set α := f '' {x | x < N + 1}

/--
The start of a reduction sequence is the first element of f, i.e. `f 0`.
Note that this always holds; a reduction sequence must contain at least one
element; there is no such thing as an empty reduction sequence with no elements.
-/
@[simp]
def reduction_seq.start (hseq: reduction_seq r N f): α := f 0

/--
Assuming N is a natural number, i.e. not infinite, `hseq.end` is the
last element of `hseq`, i.e. `f N`.
-/
@[simp]
def reduction_seq.end (N: ℕ) (hseq: reduction_seq r N f): α := f N

def reduction_seq.contains {r: Rel α α} (hseq: reduction_seq r N f) (a b: α) :=
  ∃n, f n = a ∧ f (n + 1) = b ∧ n < N

def fun_aux (N: ℕ) (f g: ℕ → α): ℕ → α :=
  fun n ↦ if (n ≤ N) then f n else g (n - N)

def reduction_seq.concat' (N₁ N₂: ℕ)
    (hseq: reduction_seq r N₁ f) (hseq': reduction_seq r N₂ g)
    (hend: f N₁ = g 0):
    reduction_seq r (N₁ + N₂) (fun_aux N₁ f g) := by
  intro n hn
  simp [fun_aux]
  norm_cast at *
  split_ifs
  · -- case within hseq
    apply hseq n (by norm_cast)
  · -- case straddling hseq and hseq'
    have: n = N₁ := by omega
    aesop
  · -- invalid straddling case (n > N₁, n + 1 ≤ N₁)
    omega
  · -- case within hseq'
    convert hseq' (n - N₁) (by norm_cast; omega) using 2
    omega

def reduction_seq.concat (N₁: ℕ) (N₂: ℕ∞)
    (hseq: reduction_seq r N₁ f) (hseq': reduction_seq r N₂ g)
    (hend: f N₁ = g 0):
    reduction_seq r (N₁ + N₂) (fun_aux N₁ f g) := by
  intro n hn
  simp [fun_aux]
  split_ifs with h₁ h₂ h₃
  · -- case within hseq
    apply hseq n (by norm_cast)
  · -- case straddling hseq and hseq'
    have: n = N₁ := by omega
    cases N₂
    all_goals (norm_cast at *; aesop)
  · -- invalid straddling case (n > N₁, n + 1 ≤ N₁)
    omega
  · -- case within hseq'
    simp at h₁ h₃ hseq
    rw [Nat.sub_add_comm h₁.le]
    apply hseq'
    cases N₂
    · simp [↓ENat.coe_lt_top]
    · norm_cast at *
      omega




end functional_def

section inductive_def

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
      | succ n => simp_all
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

end inductive_def

end Thesis
