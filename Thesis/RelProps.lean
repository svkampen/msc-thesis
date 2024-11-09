import Mathlib.Logic.Relation
import Lean.Meta.Tactic.Symm
import Mathlib.Tactic
import Thesis.Misc

namespace Thesis

open Relation

section rel_properties

postfix:max (priority := high) "∗" => Rel.reflTransGen
postfix:max (priority := high) "≡" => EqvGen
postfix:max (priority := high) "⁼" => ReflGen
postfix:max (priority := high) "⁺" => TransGen

variable {α: Type*}
variable (r s : Rel α α)

/-- Taking the inverse of a relation commutes with reflexive-transitive closure. -/
@[simp]
lemma rel_inv_star {r: Rel α α}: r.inv∗ x y ↔ r∗ y x := by
  constructor <;>
  · intro h
    induction h
    · rfl
    · apply ReflTransGen.head <;> assumption

/-- Taking the inverse of a relation commutes with transitive closure. -/
@[simp]
lemma rel_inv_plus {r: Rel α α}: r.inv⁺ x y ↔ r⁺ y x := by
  constructor <;>
  · intro h
    induction h
    · apply TransGen.single; assumption
    · apply TransGen.head <;> assumption

/--
Two relations `r` and `s` _commute weakly_ if `r a b` and `s a c`
imply the existence of a `d` s.t. `r∗ c d` and `s∗ b d`.
-/
@[simp] def weakly_commutes :=
  ∀⦃a b c: α⦄, r a b ∧ s a c → ∃d, s∗ b d ∧ r∗ c d

/--
Two relations `r` and `s` _commute_ if `r∗ a b` and `s∗ a c` imply
the existence of a `d` s.t. `r∗ c d` and `s∗ b d`.
-/
@[simp] def commutes :=
  ∀⦃a b c: α⦄, r∗ a b ∧ s∗ a c → ∃d, s∗ b d ∧ r∗ c d

@[simp] def subcommutative' (a: α) :=
  ∀⦃b c : α⦄, r a b ∧ r a c → ∃d, r⁼ b d ∧ r⁼ c d

@[simp] def subcommutative :=
  ∀⦃a b c : α⦄, r a b ∧ r a c → ∃d, r⁼ b d ∧ r⁼ c d

/-- Elementwise confluence (see `confluent`). -/
@[simp] def confluent' (a: α) : Prop :=
  ∀⦃b c : α⦄, r∗ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r∗ c d

/-- Confluence, also known as the Church-Rosser property. -/
@[simp] def confluent :=
  ∀⦃a b c: α⦄, r∗ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r∗ c d

/-- Elementwise weak confluence (see `weakly_confluent`). -/
@[simp] def weakly_confluent' (a: α) : Prop :=
  ∀⦃b c : α⦄, r a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

/-- Weak confluence, also known as local confluence or weak Church-Rosser. -/
@[simp] def weakly_confluent :=
  ∀⦃a b c : α⦄, r a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

/-- Elementwise diamond property (see `diamond_property`). -/
@[simp] def diamond_property' (a: α) : Prop :=
  ∀⦃b c: α⦄, r a b ∧ r a c → ∃d, r b d ∧ r c d

@[simp] def diamond_property : Prop :=
  ∀⦃a b c: α⦄, r a b ∧ r a c → ∃d, r b d ∧ r c d

/-- Elementwise triangle property (see `triangle_property`). -/
@[simp] def triangle_property' (a: α) : Prop :=
  ∃a', ∀b, r a b → r b a'

@[simp] def triangle_property : Prop :=
  ∀a, ∃a', ∀b, r a b → r b a'


-- Ensure that these definitions don't go out of sync:
example: subcommutative r ↔ ∀a, subcommutative' r a := by simp
example: confluent r ↔ ∀a, confluent' r a := by simp
example: weakly_confluent r ↔ ∀a, weakly_confluent' r a := by simp
example: diamond_property r ↔ ∀a, diamond_property' r a := by simp
example: triangle_property r ↔ ∀a, triangle_property' r a := by simp


/-- `ReflTransGen` is idempotent, i.e. applying it once is the same as applying it n>1 times. -/
@[simp]
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
  simp

lemma confluent_iff_star_self_commutes: confluent r ↔ commutes r∗ r∗ := by
  simp

lemma confluent_iff_star_dp: confluent r ↔ diamond_property r∗ := by
  rfl


/--
A relation `r` is _semi-confluent_ if `r∗ a b` and `r a c` imply the existence
of a `d` such that `r∗ b d` and `r∗ c d`. This differs from confluence in that
`c` must be a one-step reduct of `a`.

`semi_confluent` is equivalent to `confluent` (see `semi_confluent_iff_confluent`)
but is sometimes easier to prove as you can simply use induction on the length of `r∗ a b`.
-/
def semi_confluent := ∀{a b c}, r∗ a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

theorem semi_confluent_iff_confluent: semi_confluent r ↔ confluent r := by
  constructor
  · intro hsc
    rintro a b c ⟨hab, hac⟩
    induction hac with
    | refl => use b
    | @tail e f hae hef ih =>
        obtain ⟨d, hd⟩ := ih
        have ⟨g, hg⟩: ∃g, r∗ d g ∧ r∗ f g := hsc ⟨hd.right, hef⟩
        have hbg: r∗ b g := ReflTransGen.trans hd.left hg.left
        exact ⟨g, ⟨hbg, hg.right⟩⟩
  · rintro hc a b c ⟨hab, hac⟩
    exact hc ⟨hab, ReflTransGen.single hac⟩


/--
A relation is _conversion confluent_ if `r≡ a b` implies the existence of a
`c` such that `r∗ a c` and `r∗ b c`. It is equivalent to confluence
(see `conv_confluent_iff_confluent`).
-/
def conv_confluent := ∀{a b}, (r≡) a b → ∃c, r∗ a c ∧ r∗ b c

theorem conv_confluent_iff_confluent {r: Rel α α}: conv_confluent r ↔ confluent r := by
  constructor
  · intro hcc
    rintro a b c ⟨hab, hac⟩
    apply hcc
    apply EqvGen.trans b a c
    · exact EqvGen.symm _ _ (hab.to_equiv)
    · exact hac.to_equiv
  · intro hcon
    rintro a b hab
    induction hab with
    | rel x y rxy =>
        have hrefl : r∗ x x := ReflTransGen.refl
        exact hcon ⟨hrefl, ReflTransGen.single rxy⟩
    | refl x => exact (fun hrefl ↦ hcon ⟨hrefl, hrefl⟩) ReflTransGen.refl
    | symm x y _ ih => tauto
    | trans x y z _ _ xy_ih yz_ih =>
        obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := xy_ih, yz_ih
        have ⟨e, he⟩ : ∃e, r∗ c e ∧ r∗ d e := hcon ⟨hc.right, hd.left⟩
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
      have ⟨g, hg⟩ := hdp ⟨hed, hef⟩
      use g, hg.right, ReflTransGen.tail hcd hg.left


/--
Strong confluence, as defined by Huet (1980).

Strong confluence implies confluence, see `strongly_confluent_imp_confluent`.
-/
def strongly_confluent := ∀{a b c}, r a b ∧ r a c → ∃d, r⁼ b d ∧ r∗ c d

-- The proof of strong confluence → confluence follows the proof sketch
-- given by Huet (1980). This auxiliary def is used as an intermediate step,
-- because it provides a strong enough induction hypothesis.
private def sc_aux := ∀{a b c}, r⁼ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r⁼ c d

private lemma strongly_confluent_imp_sc_aux : strongly_confluent r → sc_aux r := by
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
      · have ⟨g, ⟨hfg, hdg⟩⟩ := hsc ⟨hef, hed⟩
        use g, ReflTransGen.trans hbd hdg, hfg

private lemma sc_aux_imp_semi_confluent : sc_aux r → semi_confluent r := by
  rintro haux a b c ⟨hab, hbc⟩
  obtain ⟨d, hd⟩ := haux ⟨ReflGen.single hbc, hab⟩
  use d, ?_, hd.left
  cases hd.right
  · exact ReflTransGen.refl
  · apply ReflTransGen.single; assumption

theorem strongly_confluent_imp_confluent : strongly_confluent r → confluent r :=
  fun h ↦ (semi_confluent_iff_confluent _).mp (sc_aux_imp_semi_confluent _ (strongly_confluent_imp_sc_aux _ h))


/-- An infinite reduction sequence described by f. -/
abbrev inf_reduction_seq (f: ℕ → α) :=
  ∀n, r (f n) (f (n + 1))

/--
In an infinite reduction sequence `inf_reduction_seq r f`,
`f (n + m)` is a reflexive-transitive reduct of `f n`.
-/
lemma inf_reduction_seq_star {r: Rel α α}: inf_reduction_seq r f → ∀n m, r∗ (f n) (f (n + m)) := by
  intro hf
  intro n m
  induction m with
  | zero => rfl
  | succ n ih =>
    apply ReflTransGen.tail ih
    apply hf

/--
A generic reduction sequence, which is finite if `N ≠ ⊤` and infinite otherwise.
-/
abbrev reduction_seq (N: ℕ∞) (f: ℕ → α) :=
  ∀(n: ℕ), (h: n < N) → r (f n) (f (n + 1))

def reduction_seq_rtg (N: ℕ∞) (f: ℕ → α) :=
  ∀(n : ℕ), (h: n < N) → r∗ (f n) (f (n + 1))


/-- Any function is a length-0 reduction sequence, containing only f 0. -/
lemma reduction_seq.refl (f: ℕ → α): reduction_seq r 0 f := by
  simp [reduction_seq]

/--
In a generic reduction sequence `reduction_seq r N f`,
`f m` is a reduct of `f n`, assuming `n < m < N + 1`.
-/
lemma reduction_seq.star {r: Rel α α} (hseq: reduction_seq r N f) (n m: ℕ) (hm: m < N + 1) (hn: n ≤ m): r∗ (f n) (f m) := by
  obtain ⟨k, hk⟩: ∃k, m = n + k := Nat.exists_eq_add_of_le (by omega)
  induction k generalizing m n hm hn with
  | zero => subst hk; rfl
  | succ k ih =>
    apply ReflTransGen.tail
    · apply ih n (n + k)
      trans (n + (k + 1)).cast
      · norm_cast; linarith
      · rw [<-hk]; exact hm
      linarith
      rfl
    · rw [hk]
      simp [<-add_assoc]
      apply hseq
      have h₁: (n + k).cast < (m.cast : ℕ∞) := by norm_cast; linarith
      have h₂: m.cast ≤ N := by exact Order.le_of_lt_add_one hm
      apply lt_of_lt_of_le h₁ h₂

lemma reduction_seq.inf_iff_inf_reduction_seq:
    reduction_seq r ⊤ f ↔ inf_reduction_seq r f := by
  simp [reduction_seq, inf_reduction_seq, lt_of_le_of_ne]


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

def fun_aux (N: ℕ) (f g: ℕ → α): ℕ → α :=
  fun n ↦ if (n ≤ N) then f n else g (n - N)

def reduction_seq.concat (N₁ N₂: ℕ)
    (hseq: reduction_seq r N₁ f) (hseq': reduction_seq r N₂ g)
    (hend: f N₁ = g 0):
    reduction_seq r (N₁ + N₂) (fun_aux N₁ f g) := by
  intro n hn
  rw [fun_aux, fun_aux]
  split <;> split
  · -- case within hseq
    apply hseq _ (by norm_cast)
  · -- case straddling hseq and hseq'
    have: n = N₁ := by omega
    simp only [this, add_tsub_cancel_left, hend]
    apply hseq'
    norm_cast at *
    omega
  · -- invalid straddling case (n > N₁, n + 1 ≤ N₁)
    omega
  · -- case within hseq'
    convert hseq' (n - N₁) (by norm_cast at *; omega) using 1
    congr
    omega

/-- An element a is a normal form in r if there are no b s.t. r a b. -/
@[reducible] def normal_form (a: α) :=
  ¬∃b, r a b

@[reducible] def weakly_normalizing' (a: α) : Prop :=
  ∃b, normal_form r b ∧ r∗ a b

/-- A relation `r` is weakly normalizing if each element can reduce to a normal form. -/
@[reducible] def weakly_normalizing : Prop :=
  ∀a, ∃b, (normal_form r b ∧ r∗ a b)

@[reducible] def strongly_normalizing' (a: α) : Prop :=
  ¬∃(f: ℕ → α), f 0 = a ∧ inf_reduction_seq r f

/-- A relation `r` is strongly normalizing if there are no infinite reduction sequences. -/
@[reducible] def strongly_normalizing : Prop :=
  ¬∃(f: ℕ → α), inf_reduction_seq r f

@[mk_iff] class IsStronglyNormalizing: Prop :=
  sn : strongly_normalizing r

/--
A relation has the _normal form property_ if, when a is equivalent to b and
b is a normal form, a reduces to b.
-/
def nf_prop :=
  ∀a b, normal_form r b → (r≡) a b → r∗ a b

/--
A relation has the _unique normal form property_ if all equivalent normal forms
`a` and `b` are equal.
-/
def unique_nf_prop :=
  ∀a b, normal_form r a ∧ normal_form r b → (r≡) a b → a = b

/--
A relation has the _unique normal form property with respect to reduction_
if all normal forms with a common expansion are equal.
-/
def unique_nf_prop_r :=
  ∀a b, normal_form r a ∧ normal_form r b → (∃c, r∗ c a ∧ r∗ c b) → a = b

/-- A relation is _complete_ if it is confluent and strongly normalizing. -/
def complete := confluent r ∧ strongly_normalizing r

/--
A relation is _semi-complete_ if it has the unique normal form property
and it is weakly normalizing.
-/
def semi_complete := unique_nf_prop r ∧ weakly_normalizing r

/--
A relation is _inductive_ if every element in a reduction sequence also reduces to some `a`.
-/
def rel_inductive := ∀{N f}, reduction_seq r N f → ∃a, ∀n < (N + 1), r∗ (f n.toNat) a

/--
A relation is _increasing_ if there exists a mapping `f: α → ℕ` which increases
with a reduction step.
-/
def increasing := ∃(f: α → ℕ), ∀{a b}, r a b → f a < f b

lemma increasing.trans: increasing r → increasing r⁺ := by
    rintro ⟨f, hf⟩
    use f
    intro a b hab
    induction hab with
    | single _ => apply hf; assumption
    | tail hab hbc ih =>
      apply lt_trans ih (hf hbc)

/-- A relation is _finitely branching_ if every element has only finitely many one-step reducts. -/
def finitely_branching :=
  ∀a, ∃(s: Finset α), ∀b, r a b → b ∈ s

/-- A relation is _acyclic_ if no element `a` is a reduct of itself. -/
def acyclic := ∀a b, r⁺ a b → a ≠ b

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
to define a step function `f: α → α` and derive `f^[·] x : ℕ → α` from it.
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
  ⟨wf_inv_imp_sn r, sn_imp_wf_inv r⟩


private lemma nwn_step (a : α): ¬weakly_normalizing' r a → ∀b, r∗ a b → ∃c, r b c := by
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
  use b, ?_, hab
  simp [normal_form]
  intro x hbx
  exact hnf x (ReflTransGen.tail hab hbx) hbx


lemma semi_complete_imp_inductive: semi_complete r → rel_inductive r := by
  rintro ⟨un, wn⟩
  intro N f hf
  have ⟨a, ha⟩ := wn (f 0)
  unfold unique_nf_prop at un

  use a
  intro n hn
  cases n with
  | top => simp at hn
  | coe n =>
    simp
    obtain ⟨b, hb⟩ := wn (f n)
    suffices ∃b, r∗ (f n) b ∧ a = b by
      · cases this; simp_all

    use b, hb.right
    apply un a b ⟨ha.left, hb.left⟩

    have haf₀: (r≡) a (f 0) := EqvGen.symm _ _ (ha.right.to_equiv)
    have hf₀fₙ: (r≡) (f 0) (f n) :=
      ReflTransGen.to_equiv <| hf.star 0 n hn <| Nat.zero_le n

    have hfₙb: (r≡) (f n) b := hb.right.to_equiv
    apply EqvGen.trans _ _ _ haf₀
    apply EqvGen.trans _ _ _ hf₀fₙ hfₙb


lemma confluent_imp_nf_prop: confluent r → nf_prop r := by
  intro hc a b hnfb hequiv
  have hconv: conv_confluent r := conv_confluent_iff_confluent.mpr hc
  obtain ⟨c, hc⟩ := hconv hequiv
  suffices hcb: c = b by
    rw [hcb] at hc; exact hc.left
  cases hc.right.cases_head
  · cc
  · exfalso
    apply hnfb
    tauto

lemma nf_imp_un: nf_prop r → unique_nf_prop r := by
  intro hnf a b ⟨hnfa, hnfb⟩ hequiv
  have := hnf a b hnfb hequiv
  cases this.cases_head
  · assumption
  · exfalso; apply hnfa; tauto

lemma semi_complete_imp_confluent: semi_complete r → confluent r := by
  rintro ⟨hun, hwn⟩
  rw [<-conv_confluent_iff_confluent]
  intro a b hab

  obtain ⟨nfa, hnfa, hranfa⟩ := hwn a
  obtain ⟨nfb, hnfb, hrbnfb⟩ := hwn b

  have hnfanfb: (r≡) nfa nfb := by
    apply EqvGen.trans
    · symm
      exact hranfa.to_equiv
    apply EqvGen.trans
    · exact hab
    · exact hrbnfb.to_equiv

  have nfa_eq_nfb := hun nfa nfb ⟨hnfa, hnfb⟩ hnfanfb
  subst nfa_eq_nfb

  exact ⟨nfa, hranfa, hrbnfb⟩

lemma inductive_increasing_imp_sn: rel_inductive r ∧ increasing r → strongly_normalizing r := by
  rintro ⟨hInd, hInc⟩
  by_contra! h

  obtain ⟨seq, hseq⟩ := h
  have hseq': reduction_seq r ⊤ seq := by exact fun n h ↦ hseq n
  obtain ⟨f, hf⟩ := hInc.trans
  obtain ⟨a, ha⟩ := hInd hseq'
  simp at ha

  have ha': ∀n, r∗ (seq n) a := fun n ↦ ha n (by simp)

  have: ∀k, 1 ≤ f (seq (k + 1)) - f (seq k) := by
    intro k
    have := hf (TransGen.single <| hseq k)
    omega

  have hgt: ∀n, n ≤ f (seq n) := by
    intro n
    induction n with
    | zero => linarith
    | succ n ih =>
      calc n + 1 ≤ f (seq n) + 1 := by omega
               _ ≤ f (seq n) + f (seq (n + 1)) - f (seq n) := by have := this n; omega
               _ = f (seq n) - f (seq n) + f (seq (n + 1)) := Nat.sub_add_comm (le_refl _)
               _ = f (seq (n + 1)) := by omega

  let k := f a

  have ha: a ≠ seq (k + 1) := by
    intro ha
    have := hgt (k + 1)
    rw [<-ha] at this
    simp [k] at this

  have hr := (reflTransGen_iff_eq_or_transGen.mp <| ha' (k + 1)).resolve_left ha
  have h: k + 1 ≤ f (seq (k + 1)) := hgt (k + 1)
  have h': f (seq (k + 1)) < k := hf hr
  linarith only [h, h']


end rel_properties


end Thesis
