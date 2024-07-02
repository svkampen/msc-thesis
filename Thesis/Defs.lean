import Mathlib.Logic.Relation
import Lean.Meta.Tactic.Symm
import Mathlib.Tactic

namespace Thesis

open Relation

/-- The symmetric closure over a relation `r`. -/
inductive SymmGen (r : α → α → Prop) : α → α → Prop
  | single {a b} : r a b → SymmGen r a b
  | symm {a b} : SymmGen r a b → SymmGen r b a

attribute [symm] SymmGen.symm

theorem SymmGen.symmetric {r : α → α → Prop} : Symmetric (SymmGen r) :=
  fun _ _ h ↦ by symm; assumption

section ars_def

/--
An Abstract Rewriting System (ARS), consisting of a set `α`, index type `I`
and an indexed set of rewrite relations on `α` over `I` (`ARS.rel`).
-/
structure ARS (α I : Type*) where
  rel : I → α → α → Prop

variable {α I}
variable (A : ARS α I)

/-- The union of the indexed relations of an ARS. -/
abbrev ARS.union_rel: α → α → Prop :=
  fun x y ↦ ∃i, A.rel i x y

/-- The reflexive-transitive closure of an ARS relation. -/
abbrev ARS.rel_star: I → α → α → Prop :=
  fun i ↦ ReflTransGen (A.rel i)

/-- The reflexive-transitive closure of the union of ARS relations. -/
abbrev ARS.union_rel_star: α → α → Prop :=
  ReflTransGen A.union_rel

/--
The convertability relation ≡ generated from the union of ARS relations.
Note that this is denoted using `=` in TeReSe, which we use for true equality.
-/
def ARS.conv: α → α → Prop :=
  EqvGen A.union_rel

/-- `x ⇒ y` means x one-step reduces to y. -/
local infixr:60 (priority := high) " ⇒ " => A.union_rel

/-- `x ⇒∗ y` means x reduces to y reflexive-transitively. -/
local infixr:60 (priority := high) " ⇒∗ " => A.union_rel_star

-- I don't love this notation, but oh well..
local notation:50 (priority := high) x:51 " ⇒[" i "]" y:50 => A.rel i x y
local notation:50 (priority := high) x:51 " ⇒∗[" i "]" y:50 => A.rel_star i x y

/--
`A: ARS α I` is a sub-ARS of `B: ARS β J` if:
- α is a subtype of β (i.e. α ~ Subtype β p for some p)
- for all a, b in α, a reduces to b in B iff a reduces to b in A
- if a is in α (i.e. `p a` holds) and a reduces to b in B, b is in α (i.e. `p b` holds).
-/
def ARS.is_sub_ars_of {p: β → Prop} {J} (A: ARS {b : β // p b} I) (B: ARS β J) :=
  (∀a b, A.union_rel a b ↔ B.union_rel a b) ∧
  (∀a b, p a ∧ B.union_rel a b → p b)

section
variable {δ} {p : δ → Prop}
variable (C: ARS δ ι) (D: ARS {d // p d} κ)

#check D.is_sub_ars_of C

end
end ars_def

section reduction_seq

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

section rel_properties

local postfix:max (priority := high) "∗" => ReflTransGen
local postfix:max (priority := high) "⇔" => EqvGen
local postfix:max (priority := high) "⁼" => ReflGen

variable {α: Type*}
variable (r s : α → α → Prop)

/--
Two relations r and s commute weakly if `r a b` and `s a c`
imply the existence of a d s.t. `r∗ c d` and `s∗ b d`.
-/
@[simp] def weakly_commutes :=
  ∀(a b c: α), r a b ∧ s a c → ∃d, s∗ b d ∧ r∗ c d

/--
Two relations r and s commute if `r∗ a b` and `s∗ a c` imply
the existence of a d s.t. `r∗ c d` and `s∗ b d`.
-/
@[simp] def commutes :=
  ∀(a b c: α), r∗ a b ∧ s∗ a c → ∃d, s∗ b d ∧ r∗ c d

/-- Elementwise confluence (see `confluent`). -/
@[simp] def confluent' (a: α) : Prop :=
  ∀(b c : α), r∗ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r∗ c d

/-- Confluence, also known as the Church-Rosser property. -/
@[simp] def confluent :=
  ∀(a b c : α), r∗ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r∗ c d

/-- Elementwise weak confluence (see `weakly_confluent`). -/
@[simp] def weakly_confluent' (a: α) : Prop :=
  ∀(b c : α), r a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

/-- Weak confluence, also known as local confluence or weak Church-Rosser. -/
@[simp] def weakly_confluent :=
  ∀(a b c : α), r a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

/-- Elementwise diamond property (see `diamond_property`). -/
@[simp] def diamond_property' (a: α) : Prop :=
  ∀(b c: α), r a b ∧ r a c → ∃d, r b d ∧ r c d

@[simp] def diamond_property : Prop :=
  ∀(a b c: α), r a b ∧ r a c → ∃d, r b d ∧ r c d

-- Ensure that these definitions don't go out of sync:
#check (by simp : confluent r ↔ ∀a, confluent' r a)
#check (by simp : weakly_confluent r ↔ ∀a, weakly_confluent' r a)
#check (by simp : diamond_property r ↔ ∀a, diamond_property' r a)

/-- `ReflTransGen` is idempotent, i.e. applying it once is the same as applying it n>1 times. -/
lemma ReflTransGen.idempotent : ReflTransGen (ReflTransGen r) x y ↔ ReflTransGen r x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ a a_ih => apply ReflTransGen.trans a_ih a
  · intro h
    apply ReflTransGen.tail
    · apply ReflTransGen.refl
    · exact h

/- A few trivial equivalences relating confluence-adjacent properties. -/
lemma confluent_iff_star_weakly_confluent: confluent r ↔ weakly_confluent r∗ := by
  simp [ReflTransGen.idempotent]

lemma confluent_iff_star_self_commutes: confluent r ↔ commutes r∗ r∗ := by
  simp [ReflTransGen.idempotent]

lemma confluent_iff_star_dp: confluent r ↔ diamond_property r∗ := by
  rfl

/--
`semi_confluent` is equivalent to `confluent` (see `semi_confluent_iff_confluent`)
but is sometimes easier to prove as you can simply use induction on the length of `r∗ a b`.
-/
def semi_confluent := ∀a b c, r∗ a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

theorem semi_confluent_iff_confluent: semi_confluent r ↔ confluent r := by
  constructor
  · intro hosc
    rintro a b c ⟨hab, hac⟩
    induction hac with
    | refl => use b
    | tail _ hef ih =>
        rename_i e f _
        obtain ⟨d, hd⟩ := ih
        have ⟨g, hg⟩: ∃g, r∗ d g ∧ r∗ f g := hosc e d f ⟨hd.right, hef⟩
        have hbg: r∗ b g := ReflTransGen.trans hd.left hg.left
        exact ⟨g, ⟨hbg, hg.right⟩⟩
  · rintro hc a b c ⟨hab, hac⟩
    exact hc _ _ _ ⟨hab, ReflTransGen.single hac⟩

/-- "Conversion confluent" (made-up term); equivalent to confluence (see `conv_confluent_iff_confluent`). -/
def conv_confluent := ∀a b, r⇔ a b → ∃c, r∗ a c ∧ r∗ b c

/-- The reflexive-transitive closure of a relation is a subset of the equivalence closure. -/
lemma lift_rt_to_eqv : ∀a b, r∗ a b → r⇔ a b := by
  intro _ _ hrs
  induction hrs using ReflTransGen.trans_induction_on with
  | ih₁ a => exact EqvGen.refl a
  | ih₂ h => exact EqvGen.rel _ _ h
  | ih₃ _ _ he₁ he₂ => exact EqvGen.trans _ _ _ he₁ he₂

theorem conv_confluent_iff_confluent: conv_confluent r ↔ confluent r := by
  constructor
  · intro hcc
    rintro a b c ⟨hab, hac⟩
    apply hcc
    apply EqvGen.trans b a c
    · exact EqvGen.symm _ _ (lift_rt_to_eqv r a b hab)
    · exact lift_rt_to_eqv r a c hac
  · intro hcon
    rintro a b hab
    induction hab with
    | rel x y rxy =>
        have hrefl : r∗ x x := ReflTransGen.refl
        exact hcon x _ _ ⟨hrefl, ReflTransGen.single rxy⟩
    | refl x => exact (fun hrefl ↦ hcon x _ _ ⟨hrefl, hrefl⟩) ReflTransGen.refl
    | symm x y _ ih => tauto
    | trans x y z _ _ xy_ih yz_ih =>
        obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := xy_ih, yz_ih
        have ⟨e, he⟩ : ∃e, r∗ c e ∧ r∗ d e := hcon _ _ _ ⟨hc.right, hd.left⟩
        exact ⟨e, ⟨ReflTransGen.trans hc.left he.left,
                   ReflTransGen.trans hd.right he.right⟩⟩

/-- The diamond property implies confluence. -/
lemma diamond_property_imp_confluent : diamond_property s → confluent s := by
  intro hdp
  apply (semi_confluent_iff_confluent s).mp
  suffices ∀a b c, s∗ a b ∧ s a c → ∃d, s b d ∧ s∗ c d by
    intro a b c h'
    obtain ⟨d, hd⟩ := this a b c h'
    use d, ReflTransGen.single hd.left, hd.right
  intro a b c ⟨hab, hac⟩
  induction hab with
  | refl => use c, hac, ReflTransGen.refl
  | tail _ hef ih =>
      rename_i e _
      obtain ⟨d, ⟨hed, hcd⟩⟩ := ih
      have ⟨g, hg⟩ := hdp _ _ _ ⟨hed, hef⟩
      use g, hg.right, ReflTransGen.tail hcd hg.left


/-- Strong confluence, as defined by Huet (1980). -/
def strongly_confluent := ∀a b c, r a b ∧ r a c → ∃d, r⁼ b d ∧ r∗ c d

-- The proof of strong confluence → confluence follows the proof sketch
-- given by Huet (1980). This auxiliary def is used as an intermediate step,
-- because it provides a strong enough induction hypothesis.
def sc_aux := ∀a b c, r⁼ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r⁼ c d

lemma strongly_confluent_imp_sc_aux : strongly_confluent r → sc_aux r := by
  intro hsc
  rintro a b c ⟨hab, hac⟩
  rcases hab with _ | hab
  case refl => use c
  induction hac with
  | refl => use b, ReflTransGen.refl, ReflGen.single hab
  | tail _ hef ih =>
      rename_i e f _
      obtain ⟨d, ⟨hbd, hed⟩⟩ := ih
      rcases hed with _ | hed
      · use f, ReflTransGen.tail hbd hef, ReflGen.refl
      · have ⟨g, ⟨hfg, hdg⟩⟩ := hsc _ _ _ ⟨hef, hed⟩
        use g, ReflTransGen.trans hbd hdg, hfg

lemma sc_aux_imp_semi_confluent : sc_aux r → semi_confluent r := by
  rintro haux a b c ⟨hab, hbc⟩
  obtain ⟨d, hd⟩ := haux _ _ _ ⟨ReflGen.single hbc, hab⟩
  use d, ?_, hd.left
  cases hd.right
  · exact ReflTransGen.refl
  · apply ReflTransGen.single; assumption

theorem strongly_confluent_imp_confluent : strongly_confluent r → confluent r :=
  fun h ↦ (semi_confluent_iff_confluent _).mp (sc_aux_imp_semi_confluent _ (strongly_confluent_imp_sc_aux _ h))

/-- An element a is a normal form in r if there are no b s.t. r a b. -/
@[reducible] def normal_form (a: α) := ¬∃b, r a b

@[reducible] def weakly_normalizing' (a: α) : Prop :=
  ∃b, normal_form r b ∧ r∗ a b

/-- A relation `r` is weakly normalizing if each element can reduce to a normal form. -/
@[reducible] def weakly_normalizing : Prop :=
  ∀a, ∃b, (normal_form r b ∧ r∗ a b)

@[reducible] def strongly_normalizing' (a: α) : Prop :=
  ¬∃(f: ℕ → α), f 0 = a ∧ ∀n, r (f n) (f (n + 1))

/-- A relation `r` is strongly normalizing if there are no infinite reduction sequences. -/
@[reducible] def strongly_normalizing : Prop :=
  ¬∃(f: ℕ → α), ∀n, r (f n) (f (n + 1))

-- For example, a reflexive relation is never strongly normalizing.
example [inst: Inhabited α]: ¬(strongly_normalizing r⁼) := by
  push_neg
  intro h
  obtain ⟨a⟩ := inst
  have ⟨_, hn⟩ := h (fun _ ↦ a)
  apply hn ReflGen.refl

/-- A relation with the diamond property has no non-trivial normal forms. -/
lemma diamond_property_imp_no_nf (hdp: diamond_property r): ∀b, (∃a, r a b) → ¬normal_form r b := by
  simp
  intro b a hab
  exact Exists.imp (by tauto) (hdp _ _ _ ⟨hab, hab⟩)

section sn_wf

/-- If a relation is well-founded, its inverse is strongly normalizing, and vice versa. -/
lemma sn_imp_wf_inv [Nonempty α] : WellFounded r ↔ strongly_normalizing (Rel.inv r) := by
  constructor
  -- WellFounded -> strongly_normalizing is easy
  · rintro hwf ⟨f, hf⟩
    obtain ⟨a, ⟨hmem, hmin⟩⟩ := hwf.has_min (f '' Set.univ) (Set.image_nonempty.mpr Set.univ_nonempty)
    obtain ⟨n, rfl⟩: ∃n, f n = a := by rwa [<-Set.mem_range, <-Set.image_univ]
    exact hmin (f (n + 1)) (by simp only [Set.image_univ, Set.mem_range, exists_apply_eq_apply]) (hf n)

  /-
  strongly_normalizing → WellFounded is more difficult.
  We first translate WellFounded to its equivalent "relation has a minimum on all sets"
  Then, we take the contrapositive. That way, we get a "step" formula, telling us there
  is a next element x ∈ s for each element m ∈ s which is related through r x m.

  `choose!` transforms this formula into a function along with hypotheses on it.
  This is really the crucial step, and the one I don't understand very well.

  Afterwards, it is an easy induction.
  -/
  · intro hsn
    rw [WellFounded.wellFounded_iff_has_min]
    contrapose! hsn with hwf
    obtain ⟨s, ⟨⟨x, hx⟩, hstep⟩⟩ := hwf

    choose! f hmem hrel using hstep

    intro h
    have ⟨n, hn⟩ := h (f^[·] x)
    have : ∀N, f^[N] x ∈ s := by
      clear hn
      intro N
      induction N with
      | zero => exact hx
      | succ n ih =>
        rw [Function.iterate_succ', Function.comp]
        apply hmem _ ih

    apply hn
    rw [Function.iterate_succ', Function.comp]
    exact hrel _ (this n)

end sn_wf


lemma nwn_step (a : α): ¬weakly_normalizing' r a → ∀b, r∗ a b → ∃c, r b c := by
  intro hwn
  contrapose! hwn
  obtain ⟨b, hb⟩ := hwn; use b
  simp_all only [not_exists, not_false_eq_true, implies_true, and_self]

lemma strongly_normalizing_imp_weakly_normalizing {r: α → α → Prop}: strongly_normalizing r → weakly_normalizing r := by
  unfold weakly_normalizing strongly_normalizing
  intro hsn
  contrapose! hsn with hwn
  obtain ⟨a, ha⟩ := hwn

  choose! f h₁ using nwn_step r a (by simp [weakly_normalizing']; itauto)

  have: ∀N, r∗ a (f^[N] a) := by
    intro N; induction N with
    | zero => simp [ReflTransGen.refl]
    | succ n ih =>
        rw [Function.iterate_succ', Function.comp]
        exact ReflTransGen.tail ih (h₁ _ ih)

  use (f^[·] a)
  intro N
  rw [Function.iterate_succ', Function.comp]
  exact h₁ _ (this N)

def empty_rel {α}: α → α → Prop := fun _ _ ↦ False

def nonempty_rel := ∃a b, r a b

lemma empty_rel_is_sn_and_dp: (@strongly_normalizing α empty_rel ∧ @diamond_property α empty_rel) := by
  simp [empty_rel]

lemma nonempty_wn_rel_imp_not_dp (hn: nonempty_rel r) : weakly_normalizing r → ¬diamond_property r := by
  intro hw hdp
  obtain ⟨a, b, hab⟩ := hn
  obtain ⟨c, ⟨hnf, hstep⟩⟩ := hw a

  cases hstep with
  | refl => simp_all only [not_exists, not_forall, diamond_property, and_imp]
  | tail h₁ h₂ => exact hnf (Exists.imp (by tauto) (hdp _ _ _ ⟨h₂, h₂⟩))

section ex1_3_1

variable (hrs: Subrelation r s) (hsr: Subrelation s r∗) (hdp: diamond_property s)

lemma aux {a b: α}: r∗ a b ↔ s∗ a b := by
  constructor
  · intro hr
    induction hr with
    | refl => exact ReflTransGen.refl
    | tail _ hr₂ ih => exact ReflTransGen.tail ih (hrs hr₂)
  · intro hs
    induction hs with
    | refl => exact ReflTransGen.refl
    | tail _ hs₂ ih => exact ReflTransGen.trans ih (hsr hs₂)

example: confluent r := by
  intro a b c
  have aux' := @aux _ r s hrs hsr
  rw [aux', aux']
  intro h
  have hcs := diamond_property_imp_confluent _ hdp
  have ⟨d, hd⟩ := hcs _ _ _ h
  use d
  rw [aux', aux']
  exact hd

end ex1_3_1

end rel_properties


end Thesis
