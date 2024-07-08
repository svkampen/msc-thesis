import Mathlib.Logic.Relation
import Lean.Meta.Tactic.Symm
import Mathlib.Tactic

namespace Thesis

open Relation

/-- The symmetric closure over a relation `r`. -/
inductive SymmGen (r : Rel α α) : Rel α α
  | single {a b} : r a b → SymmGen r a b
  | symm {a b} : SymmGen r a b → SymmGen r b a

attribute [symm] SymmGen.symm

theorem SymmGen.symmetric {r : Rel α α} : Symmetric (SymmGen r) :=
  fun _ _ h ↦ by symm; assumption

section rel_properties

postfix:max (priority := high) "∗" => ReflTransGen
postfix:max (priority := high) "⇔" => EqvGen
postfix:max (priority := high) "⁼" => ReflGen
postfix:max (priority := high) "⁺" => TransGen

variable {α: Type*} [Nonempty α]
variable (r s : Rel α α)

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

@[simp] def subcommutative' (a: α) :=
  ∀(b c : α), r a b ∧ r a c → ∃d, r⁼ b d ∧ r⁼ c d

@[simp] def subcommutative :=
  ∀(a b c : α), r a b ∧ r a c → ∃d, r⁼ b d ∧ r⁼ c d

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

@[simp] def triangle_property' (a: α) : Prop :=
  ∃a', ∀b, r a b → r b a'

@[simp] def triangle_property : Prop :=
  ∀a, ∃a', ∀b, r a b → r b a'

-- Ensure that these definitions don't go out of sync:
#check (by simp : subcommutative r ↔ ∀a, subcommutative' r a)
#check (by simp : confluent r ↔ ∀a, confluent' r a)
#check (by simp : weakly_confluent r ↔ ∀a, weakly_confluent' r a)
#check (by simp : diamond_property r ↔ ∀a, diamond_property' r a)
#check (by simp : triangle_property r ↔ ∀a, triangle_property' r a)

/-- `ReflTransGen` is idempotent, i.e. applying it once is the same as applying it n>1 times. -/
lemma ReflTransGen.idempotent : r∗∗ x y ↔ r∗ x y := by
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
lemma diamond_property_imp_confluent : diamond_property r → confluent r := by
  intro hdp
  apply (semi_confluent_iff_confluent r).mp
  suffices ∀a b c, r∗ a b ∧ r a c → ∃d, r b d ∧ r∗ c d by
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

/-- An infinite reduction sequence described by f. -/
@[reducible] def inf_reduction_seq (f: ℕ → α) := ∀n, r (f n) (f (n + 1))

@[reducible] def fin_reduction_seq {n} (f: Fin n → α) := ∀N, (h: N < (n - 1)) → r (f ⟨N, by omega⟩) (f ⟨N + 1, by omega⟩)

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
  ¬∃(f: ℕ → α), inf_reduction_seq r f


@[mk_iff] class IsStronglyNormalizing: Prop :=
  sn : strongly_normalizing r

/-- Normal Form property: if a is equivalent to b and b is a normal form, a reduces to b. -/
def NF_prop :=
  ∀a b, normal_form r b → r⇔ a b → r∗ a b

/-- Unique Normal form property: all equivalent normal forms a and b are equal. -/
def UN_prop :=
  ∀a b, normal_form r a ∧ normal_form r b → r⇔ a b → a = b

/-- Unique Normal form property w.r.t. reduction: all normal forms with a common expansion are equal. -/
def UNr_prop :=
  ∀a b, normal_form r a ∧ normal_form r b → (∃c, r∗ c a ∧ r∗ c b) → a = b

def complete := confluent r ∧ strongly_normalizing r

def semi_complete := UN_prop r ∧ weakly_normalizing r

/--
A relation is _inductive_ if every element in an infinite reduction sequence also reduces to some a.
Note that this is specifically about infinite reduction sequences. There may need to be some other
definition for finite reduction sequences; I don't know when inductive relations are used yet :P.
-/
def inf_inductive := ∀f, inf_reduction_seq r f → ∃a, ∀n, r∗ (f n) a

def increasing := ∃(f: α → ℕ), ∀a b, r a b → f a < f b

def finitely_branching :=
  ∀a, ∃(s: Finset α), ∀b, r a b → b ∈ s

-- For example, a reflexive relation is never strongly normalizing.
example [inst: Inhabited α]: ¬(strongly_normalizing r⁼) := by
  push_neg
  intro h
  obtain ⟨a⟩ := inst
  simp [inf_reduction_seq] at h
  obtain ⟨_, hn⟩ := h (fun _ ↦ a)
  apply hn ReflGen.refl

/-- A relation with the diamond property has no non-trivial normal forms. -/
lemma diamond_property_imp_no_nf (hdp: diamond_property r): ∀b, (∃a, r a b) → ¬normal_form r b := by
  simp
  intro b a hab
  exact Exists.imp (by tauto) (hdp _ _ _ ⟨hab, hab⟩)

/-- If r⁻¹ is well-founded, then r is strongly normalizing. -/
lemma wf_inv_imp_sn : WellFounded (r.inv) → strongly_normalizing r := by
  rintro hwf ⟨f, hf⟩
  obtain ⟨a, ⟨hmem, hmin⟩⟩ := hwf.has_min (f '' Set.univ) (Set.image_nonempty.mpr Set.univ_nonempty)
  obtain ⟨n, rfl⟩: ∃n, f n = a := by rwa [<-Set.mem_range, <-Set.image_univ]
  exact hmin (f (n + 1)) (by simp only [Set.image_univ, Set.mem_range, exists_apply_eq_apply]) (hf n)

/--
If r is strongly normalizing, then r⁻¹ is well-founded.

This is more difficult than the inverse (`wf_inv_imp_sn`).

We first translate WellFounded to its equivalent "relation has a minimum on all sets"
Then, we take the contrapositive. That way, we get a "step" formula, telling us there
is a next element `x ∈ s` for each element `m ∈ s` which is related through `r x m`.

`choose!` transforms this formula into a function along with hypotheses on it.
This is really the crucial step. I previously attempted to directly define a
recursive function `f: ℕ → α` which provides the witness for strongly_normalizing,
but you get into all sorts of problems attempting this. It is much more effective
to define a step function `f: α → α` and derive `f^[n] x : ℕ → α` from it.
This can be done manually (see below), but `choose!` is obviously much faster.

Afterwards, it is an easy induction.
-/
lemma sn_imp_wf_inv : strongly_normalizing r → WellFounded (r.inv) := by
  intro hsn
  rw [WellFounded.wellFounded_iff_has_min]
  contrapose! hsn with hwf
  obtain ⟨s, ⟨⟨x, hx⟩, hstep⟩⟩ := hwf

  push_neg

  -- let f : α → α := fun m ↦ if hm : (m ∈ s) then Classical.choose (hstep m hm) else x

  -- have hmem: ∀m ∈ s, f m ∈ s := by
  --   intro m hm
  --   simp [f, dif_pos hm]
  --   apply (Classical.choose_spec (hstep m hm)).1

  -- have hrel: ∀ m ∈ s, r m (f m) := by
  --   intro m hm
  --   simp [f, dif_pos hm]
  --   apply (Classical.choose_spec (hstep m hm)).2

  -- or, equivalently:
  choose! f hmem hrel using hstep

  use (f^[·] x)
  have : ∀N, f^[N] x ∈ s := Function.Iterate.rec _ hmem hx

  unfold inf_reduction_seq
  intro n
  simp only [Function.iterate_succ', Function.comp]
  exact hrel _ (this n)

/-- If a relation is strongly normalizing, its inverse is well-founded, and vice versa. -/
lemma sn_iff_wf_inv: WellFounded (r.inv) ↔ strongly_normalizing (r) :=
  Iff.intro (wf_inv_imp_sn r) (sn_imp_wf_inv r)


lemma nwn_step (a : α): ¬weakly_normalizing' r a → ∀b, r∗ a b → ∃c, r b c := by
  intro hwn
  contrapose! hwn
  obtain ⟨b, hb⟩ := hwn; use b
  simp_all only [not_exists, not_false_eq_true, implies_true, and_self]

/-- Strong normalization implies weak normalization. -/
lemma strongly_normalizing_imp_weakly_normalizing {r: Rel α α}: strongly_normalizing r → weakly_normalizing r := by
  unfold weakly_normalizing strongly_normalizing
  intro hsn
  contrapose! hsn with hwn
  obtain ⟨a, ha⟩ := hwn

  choose! f h₁ using nwn_step r a (by simp [weakly_normalizing']; itauto)

  have: ∀N, r∗ a (f^[N] a) := Function.Iterate.rec _ (fun b h ↦ ReflTransGen.tail h (h₁ b h)) ReflTransGen.refl

  use (f^[·] a)
  intro N
  simp only [Function.iterate_succ', Function.comp]
  exact h₁ _ (this N)

/- A shorter proof, making use of well-foundedness. -/
lemma strongly_normalizing_imp_weakly_normalizing₂ {r: Rel α α}: strongly_normalizing r → weakly_normalizing r := by
  intro hsn a
  obtain ⟨b, ⟨hab, hnf⟩⟩ := (sn_imp_wf_inv _ hsn).has_min {b | r∗ a b} (Set.nonempty_of_mem ReflTransGen.refl)
  use b, ?nf, hab
  simp [normal_form]
  intro x hbx
  exact hnf x (ReflTransGen.tail hab hbx) hbx

def empty_rel {α}: Rel α α := fun _ _ ↦ False

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



end rel_properties


end Thesis
