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

def reduction_seq.concat {r} {N₁: ℕ} {N₂: ℕ∞}
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

def reduction_seq.tail (hseq: reduction_seq r N f):
    reduction_seq r (N - 1) (fun n ↦ f (n + 1)) := by
  cases N with
  | top => aesop
  | coe a =>
    cases a <;>
    · norm_cast
      aesop

def reduction_seq.flatten {N: ℕ} (hseq: reduction_seq r∗ N f):
    ∃(N': ℕ) (f': ℕ → α) (hseq': reduction_seq r N' f'),
      hseq.start = hseq'.start ∧ hseq.end = hseq'.end := by
  induction N generalizing f with
  | zero =>
    use 0, f, refl r f
    aesop
  | succ n ih =>
    obtain ⟨N₂, f₂, hseq₂, h⟩ := ih hseq.tail
    simp at h ⊢
    have := hseq 0 (by simp)
    obtain ⟨N₁, f₁, hseq₁, h'⟩ := reduction_seq.from_reflTrans this
    have := hseq₁.concat hseq₂ (by aesop)
    norm_cast at this
    use N₁ + N₂, fun_aux N₁ f₁ f₂
    rw [fun_aux]
    and_intros
    · aesop
    · intro n hn
      apply this
      norm_cast
    · simp [fun_aux]
      split_ifs with h
      · subst h
        simp at h' ⊢
        cc
      · tauto

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

attribute [simp] ReductionSeq.refl
attribute [aesop 25% unsafe] ReductionSeq.head

variable {r: Rel α α}

namespace ReductionSeq

def elems (_: ReductionSeq r x y ss) := x :: (ss.map RSStep.stop)

def elems' (_: ReductionSeq r x y ss) := ss.map RSStep.start ++ [y]

lemma elems_eq_elems' (hseq: ReductionSeq r x y ss): hseq.elems = hseq.elems' := by
  induction hseq with
  | refl => rfl
  | head hstep hseq ih =>
    simp_all [elems, elems']

lemma y_elem (hseq: ReductionSeq r x y ss): y ∈ hseq.elems := by
  induction hseq with
  | refl => simp [elems]
  | @head x y z ss step seq ih =>
    simp [elems] at ih ⊢
    tauto

@[aesop 10% unsafe]
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

lemma to_reflTrans (hseq: ReductionSeq r x y ss): r∗ x y := by
  apply exists_iff_rel_star.mpr
  use ss

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

lemma get_step (hseq: ReductionSeq r x y ss) (s: RSStep α) (hs: s ∈ ss):
    r s.start s.stop := by
  induction hseq with
  | refl => contradiction
  | @head x y z ss step seq ih => aesop

@[simp]
lemma empty_iff: ReductionSeq r x y [] ↔ x = y := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact refl

lemma last (hseq: ReductionSeq r x y (ss' ++ [b])): b.stop = y := by
  generalize hss: ss' ++ [b] = ss
  rw [hss] at hseq
  induction hseq generalizing ss' b with
  | refl => aesop
  | head hstep hseq ih =>
    rename_i x y z ss
    cases ss'
    · aesop
    · aesop

def has_peak (hseq: ReductionSeq (SymmGen r) x y ss) :=
  ∃(n: ℕ) (h: n < ss.length - 1), r ss[n].stop ss[n].start ∧ r ss[n + 1].start ss[n + 1].stop

def steps_reversed: List (RSStep α) → List (RSStep α)
| [] => []
| (x::xs) => steps_reversed xs ++ [{ start := x.stop, stop := x.start }]

lemma steps_reversed_append:
      steps_reversed (xs ++ ys) = steps_reversed ys ++ steps_reversed xs
    := by
  induction xs with
  | nil => simp!
  | cons head tail ih =>
    simp! [ih]

lemma steps_reversed_mem (hs: s ∈ ss): ⟨s.stop, s.start⟩ ∈ (steps_reversed ss) := by
  induction ss with
  | nil => contradiction
  | cons head tail ih =>
    simp at hs
    rcases hs with (hs | hs)
    · simp! [hs]
    · simp only [steps_reversed]
      aesop

lemma steps_reversed_add: steps_reversed (ss ++ [s]) = ⟨s.stop, s.start⟩::(steps_reversed ss) := by
  induction ss generalizing s with
  | nil => rfl
  | cons head tail ih =>
    simp! [ih]

@[simp]
lemma steps_reversed_reversed: steps_reversed (steps_reversed ss) = ss := by
  induction ss with
  | nil => rfl
  | cons head tail ih =>
    simp! [steps_reversed_add]
    exact ih

lemma step_start_stop (hseq: ReductionSeq r x y ss) (n: ℕ) (hn: n < ss.length - 1):
    ss[n].stop = ss[n + 1].start := by
  induction hseq generalizing n with
  | refl => contradiction
  | head hstep hseq ih =>
    cases hseq
    · contradiction
    rcases n with (_ | n) <;> aesop

lemma take (hseq : ReductionSeq r x y ss) (n : ℕ) (hn : n ≤ ss.length):
    ReductionSeq r x (hseq.elems[n]'(by simp [elems]; omega)) (List.take n ss) := by
  induction hseq generalizing n with
  | refl => simp_all [elems]
  | head hstep hseq ih =>
    simp at hn
    simp [elems]
    cases n <;> aesop

lemma drop (hseq: ReductionSeq r x y ss) (n: ℕ) (hn: n ≤ ss.length):
    ReductionSeq r (hseq.elems[n]'(by simp [elems]; omega)) y (ss.drop n) := by
  induction hseq generalizing n with
  | refl => simp [elems]
  | head hstep hseq ih =>
    cases n <;> aesop

lemma to_symmgen (hseq: ReductionSeq r x y ss):
    ReductionSeq (SymmGen r) x y ss := by
  induction hseq with
  | refl => simp
  | head hstep hseq ih =>
    aesop (add unsafe 25% SymmGen.fw_step)

lemma symmgen_reverse (hseq: ReductionSeq (SymmGen r) x y ss):
    ReductionSeq (SymmGen r) y x (steps_reversed ss) := by
  induction hseq with
  | refl => simp!
  | head hstep hseq ih =>
    simp_all!
    apply tail
    exact ih
    cases hstep
    · apply SymmGen.bw_step
      assumption
    · apply SymmGen.fw_step
      assumption

lemma exists_iff_rel_conv: (r≡) x y ↔ ∃ss, ReductionSeq (SymmGen r) x y ss := by
  constructor <;> intro h
  · induction h with
    | rel x y step => use [⟨x, y⟩]; aesop
    | refl x => use []; aesop
    | symm x y h ih =>
      obtain ⟨ss, hss⟩ := ih
      use (steps_reversed ss)
      exact symmgen_reverse hss
    | trans x y z hl hr ih1 ih2 =>
      obtain ⟨ss₁, h₁⟩ := ih1
      obtain ⟨ss₂, h₂⟩ := ih2
      have := h₁.concat h₂
      apply Exists.intro
      use this
  · obtain ⟨ss, hseq⟩ := h
    induction hseq with
    | refl => rfl
    | head hstep hseq ih =>
      rename_i x y z ss
      cases hstep with
      | fw_step hstep =>
        apply EqvGen.trans x y z
        apply EqvGen.rel x y hstep
        exact ih
      | bw_step hstep =>
        apply EqvGen.trans x y z
        apply EqvGen.symm
        exact EqvGen.rel y x hstep
        exact ih

lemma no_peak_cases (hseq: ReductionSeq (SymmGen r) x y ss) (hnp: ¬hseq.has_peak):
    ReductionSeq r x y ss ∨ ReductionSeq r y x (steps_reversed ss) ∨ ∃ss₁ ss₂, (
      ss = ss₁ ++ ss₂ ∧ ss₁ ≠ [] ∧ ss₂ ≠ [] ∧ ∃z, (ReductionSeq r x z ss₁ ∧ ReductionSeq r y z (steps_reversed ss₂))
    ) := by
  induction hseq with
  | refl =>
    left; simp
  | head hstep hseq ih =>
    rename_i x y z ss'
    have hnp': ¬hseq.has_peak := by
      simp [has_peak] at hnp ⊢
      intro x hx
      have := hnp (x + 1) (by omega)
      simpa
    specialize ih hnp'
    cases hseq
    · cases hstep
      · left; simp_all [ReductionSeq.head]
      · right; left; simp_all! [ReductionSeq.head]
    rcases ih with h | h | h <;> rcases hstep with hstep | hstep
    · left; apply ReductionSeq.head hstep h
    · refine (hnp ?_).elim
      have := h.get_step
      use 0
      aesop
    · right; right
      rename_i y' ss' hsg hseq
      use [⟨x, y⟩], ⟨y, y'⟩::ss'
      simp
      use y
      aesop
    · right; left
      rw [steps_reversed]
      aesop
    · right; right
      obtain ⟨ss₁, ss₂, heq, hne₁, hne₂, z', hseq₁, hseq₂⟩ := h
      use ⟨x, y⟩::ss₁, ss₂
      aesop
    · exfalso
      apply hnp
      obtain ⟨ss₁, ss₂, heq, hne₁, hne₂, z', hseq₁, hseq₂⟩ := h
      have := hseq₁.get_step
      use 0
      simp
      use hstep
      rename_i y' _ _ _
      cases ss₁ with
      | nil => contradiction
      | cons head tail =>
        have: ⟨y, y'⟩ = head := by aesop
        aesop

lemma reduct_of_not_peak (hseq: ReductionSeq (SymmGen r) x y ss) (hnp: ¬hseq.has_peak):
    ∃d, r∗ x d ∧ r∗ y d := by
  have := hseq.no_peak_cases hnp
  rcases this with h | h | h
  · use y, h.to_reflTrans
  · use x, ReflTransGen.refl, h.to_reflTrans
  · obtain ⟨ss₁, ss₂, heq, hne₁, hne₂, z, hseq₁, hseq₂⟩ := h
    use z, hseq₁.to_reflTrans, hseq₂.to_reflTrans


end ReductionSeq

end inductive_def

end Thesis
