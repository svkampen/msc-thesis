import Mathlib.Logic.Relation
import Lean.Meta.Tactic.Symm
import Mathlib.Tactic
import Thesis.ReductionSeq

/-!

# Basic properties of rewrite relations

We define the basic properties of rewrite relations (commutation, confluence,
normalization, as well as various variants of these). Additionally, we prove
various theorems that relate these properties to one another.

-/

namespace Thesis

open Relation

section rel_properties

variable {α: Type*}
variable (r s : Rel α α)

/-- Two relations `r` and `s` _commute weakly_ if any one-step reducts `b`
    (via `r`) and `c` (via `s`) of `a` have a common reduct `d`. -/
abbrev weakly_commutes :=
  ∀⦃a b c: α⦄, r a b ∧ s a c → ∃d, s∗ b d ∧ r∗ c d

/-- Two relations `r` and `s` _commute_ if any reducts `b` (via `r`)
    and `c` (via `s`) of `a` have a common reduct `d`. -/
abbrev commutes :=
  ∀⦃a b c: α⦄, r∗ a b ∧ s∗ a c → ∃d, s∗ b d ∧ r∗ c d

/-- A relation `r` is _subcommutative_ if any one-step reducts `b` and `c`
    of `a` have a common reduct `d`, which may be equal to `b` or `c`. -/
abbrev subcommutative :=
  ∀⦃a b c : α⦄, r a b ∧ r a c → ∃d, r⁼ b d ∧ r⁼ c d

/-- A relation `r` is _confluent_ if any reducts `b` and `c` of `a` have
    a common reduct `d`. -/
abbrev confluent :=
  ∀⦃a b c: α⦄, r∗ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r∗ c d

/-- Confluence for a specific element `a: α` (see `confluent`). -/
abbrev confluent' (a: α) : Prop :=
  ∀⦃b c : α⦄, r∗ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r∗ c d

/-- A relation `r` is _weakly confluent_ (or _locally confluent_) if
    any one-step reducts `b` and `c` of `a` have a common reduct `d`. -/
abbrev weakly_confluent :=
  ∀⦃a b c : α⦄, r a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

/-- The _diamond property_ holds if any one-step reducts `b` and `c`
    of `a` have a common one-step reduct `d`. -/
abbrev diamond_property : Prop :=
  ∀⦃a b c: α⦄, r a b ∧ r a c → ∃d, r b d ∧ r c d

/-- The _triangle property_ holds if every element `a` has a two-step reduct
    `a'` which can be reached via all one-step reducts `b`. -/
abbrev triangle_property : Prop :=
  ∀a, ∃a', ∀b, r a b → r b a'


-- Ensure that these definitions don't go out of sync:
example: confluent r ↔ ∀a, confluent' r a := by simp


/- A few trivial equivalences relating confluence-adjacent properties. -/
lemma confluent_iff_star_weakly_confluent:
    confluent r ↔ weakly_confluent r∗ := by
  simp [reflTransGen_idem, confluent, weakly_confluent]

lemma confluent_iff_star_self_commutes:
    confluent r ↔ commutes r∗ r∗ := by
  simp [reflTransGen_idem, confluent, commutes]

lemma confluent_iff_star_dp:
    confluent r ↔ diamond_property r∗ := by
  rfl


/--
A relation `r` is _semi-confluent_ if `r∗ a b` and `r a c` imply the existence of a `d` such that
`r∗ b d` and `r∗ c d`. This differs from confluence in that `c` must be a one-step reduct of `a`.

`semi_confluent` is equivalent to `confluent` (see `semi_confluent_iff_confluent`)
but is sometimes easier to prove as you can simply use induction on the length of `r∗ a b`.
-/
def semi_confluent :=
  ∀⦃a b c⦄, r∗ a b ∧ r a c → ∃d, r∗ b d ∧ r∗ c d

/-- Semi-confluence is equivalent to confluence. -/
theorem semi_confluent_iff_confluent {r: Rel α α}:
    semi_confluent r ↔ confluent r := by
  constructor
  · intro hsc
    rintro a b c ⟨hab, hac⟩
    induction hac with
    | refl => use b
    | @tail e f _ hef ih =>
        obtain ⟨d, hd⟩ := ih
        have ⟨g, hg⟩: ∃g, r∗ d g ∧ r∗ f g := hsc ⟨hd.right, hef⟩
        have hbg: r∗ b g := ReflTransGen.trans hd.left hg.left
        exact ⟨g, ⟨hbg, hg.right⟩⟩
  · rintro hc a b c ⟨hab, hac⟩
    exact hc ⟨hab, ReflTransGen.single hac⟩


/--
A relation is _conversion confluent_ if `r≡ a b` implies the existence of a `c` such that
`r∗ a c` and `r∗ b c`. It is equivalent to confluence (see `conv_confluent_iff_confluent`).

This is also called the _Church-Rosser property_ -- since Terese identifies confluence and the
Church-Rosser property, we use the novel name conversion confluence here.
-/
def conv_confluent :=
  ∀⦃a b⦄, (r≡) a b → ∃c, r∗ a c ∧ r∗ b c

/-- Conversion confluence is equivalent to confluence. -/
theorem conv_confluent_iff_confluent {r: Rel α α}:
    conv_confluent r ↔ confluent r := by
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
lemma confluent_of_diamond_property:
    diamond_property r → confluent r := by
  intro hdp
  apply semi_confluent_iff_confluent.mp
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

Strong confluence implies confluence, see `confluent_of_strongly_confluent`.
-/
def strongly_confluent :=
  ∀⦃a b c⦄, r a b ∧ r a c → ∃d, r⁼ b d ∧ r∗ c d

-- The proof of strong confluence → confluence follows the proof sketch
-- given by Huet (1980). This auxiliary def is used as an intermediate step,
-- because it provides a strong enough induction hypothesis.
private def sc_aux :=
  ∀⦃a b c⦄, r⁼ a b ∧ r∗ a c → ∃d, r∗ b d ∧ r⁼ c d

@[local simp]
private lemma sc_aux_of_strongly_confluent:
    strongly_confluent r → sc_aux r := by
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

@[local simp]
private lemma semi_confluent_of_sc_aux:
    sc_aux r → semi_confluent r := by
  rintro haux a b c ⟨hab, hbc⟩
  obtain ⟨d, hd⟩ := haux ⟨ReflGen.single hbc, hab⟩
  use d, ?_, hd.left
  cases hd.right
  · exact ReflTransGen.refl
  · apply ReflTransGen.single; assumption

/-- Any relation that is strongly confluent is confluent. -/
theorem confluent_of_strongly_confluent:
    strongly_confluent r → confluent r := by
  intros; simp [<-semi_confluent_iff_confluent, *]

/-- An element `a` is a _normal form_ in `r` if there are no `b` s.t. `r a b`. -/
abbrev normal_form (a: α) :=
  ¬∃b, r a b

abbrev weakly_normalizing' (a: α) : Prop :=
  ∃b, normal_form r b ∧ r∗ a b

/-- A relation is _weakly normalizing_ if all elements can reduce to a normal form. -/
abbrev weakly_normalizing : Prop :=
  ∀a, ∃b, (normal_form r b ∧ r∗ a b)

abbrev strongly_normalizing' (a: α) : Prop :=
  ¬∃(f: ℕ → α), f 0 = a ∧ reduction_seq r ⊤ f

/-- A relation is _strongly normalizing_ if it admits no infinite reduction sequences. -/
abbrev strongly_normalizing : Prop :=
  ¬∃(f: ℕ → α), reduction_seq r ⊤ f

/-- A relation has the _normal form property_ if a reduces to b if b is a normal form and a ≡ b. -/
def normal_form_property :=
  ∀a b, normal_form r b → (r≡) a b → r∗ a b

/--
A relation has the _unique normal form property_ if all equivalent normal forms
`a` and `b` are equal.
-/
def unique_normal_form_property :=
  ∀a b, normal_form r a ∧ normal_form r b → (r≡) a b → a = b

/--
A relation has the _unique normal form property with respect to reduction_
if all normal forms with a common expansion are equal.
-/
def unique_nf_prop_r :=
  ∀a b c, normal_form r a ∧ normal_form r b → r∗ c a ∧ r∗ c b → a = b

/-- A relation is _complete_ if it is confluent and strongly normalizing. -/
def complete := confluent r ∧ strongly_normalizing r

/--
A relation is _semi-complete_ if it has the unique normal form property
and it is weakly normalizing.
-/
def semi_complete := unique_normal_form_property r ∧ weakly_normalizing r

/--
A relation is _inductive_ if, for every reduction sequence, there exists
an element `a` that is a reduct of every element in the sequence.

Since inductive is a Lean keyword, we use the name `rel_inductive`.
-/
def rel_inductive :=
  ∀{N f} (hseq: reduction_seq r N f), ∃a, ∀b ∈ hseq.elems, r∗ b a

/--
A relation is _increasing_ if there exists a mapping `f: α → ℕ` which increases
with a reduction step.
-/
def increasing := ∃(f: α → ℕ), ∀{a b}, r a b → f a < f b

/-- If `r` is increasing, so is its transitive closure `r⁺`. -/
lemma increasing_trans_of_increasing {r: Rel α α}: increasing r → increasing r⁺ := by
    rintro ⟨f, hf⟩
    use f
    intro a b hab
    induction hab with
    | single _ => apply hf; assumption
    | tail _ hbc ih =>
      apply lt_trans ih (hf hbc)

/-- A relation is _finitely branching_ if every element has only finitely many one-step reducts. -/
def finitely_branching :=
  ∀a, ∃(s: Finset α), ∀b, r a b → b ∈ s

/-- A relation is _acyclic_ if no element `a` is a reduct of itself. -/
def acyclic := ∀a b, r⁺ a b → a ≠ b

/-- If r⁻¹ is well-founded, then r is strongly normalizing. -/
lemma sn_of_wf_inv: WellFounded (r.inv) → strongly_normalizing r := by
  intro hwf ⟨f, hseq⟩
  generalize h: f 0 = a
  induction a using hwf.induction generalizing f with
  | h a ih =>
    subst h
    apply ih (f 1) (hseq 0 ENat.top_pos) (fun n ↦ f (n + 1))
    all_goals aesop

/--
If r is strongly normalizing, then r⁻¹ is well-founded.

Take the contrapositive, i.e. ¬WF → ¬SN. Assume `r` is not well-founded. Then it has an
inaccessible element. Any inaccessible element must have a descendent which is inaccessible.
This leads to an infinite sequence of inaccessible elements. Hence, `r` cannot be strongly normalizing.
-/
lemma wf_inv_of_sn: strongly_normalizing r → WellFounded (r.inv) := by
  intro hsn
  constructor
  contrapose! hsn with hacc
  push_neg
  obtain ⟨a, ha⟩ := hacc

  have acc_step: ∀a, ¬Acc r.inv a → ∃x, r.inv x a ∧ ¬Acc r.inv x := by
    intro a
    contrapose!
    exact Acc.intro a

  choose! f hf hf' using acc_step

  use (f^[·] a)
  have: ∀N, ¬Acc r.inv (f^[N] a) := Function.Iterate.rec _ hf' ha

  simpa [↓Function.iterate_succ'] using (fun n ↦ hf _ (this n))

/-- If a relation is strongly normalizing, its inverse is well-founded, and vice versa. -/
lemma sn_iff_wf_inv: WellFounded (r.inv) ↔ strongly_normalizing (r) :=
  ⟨sn_of_wf_inv r, wf_inv_of_sn r⟩

/-- Strong normalization implies weak normalization. -/
lemma wn_of_sn {r: Rel α α}: strongly_normalizing r → weakly_normalizing r := by
  intro hsn a
  obtain ⟨b, ⟨hab, hnf⟩⟩ :=
    (wf_inv_of_sn _ hsn).has_min {b | r∗ a b} (Set.nonempty_of_mem ReflTransGen.refl)
  use b, ?_, hab
  simp [normal_form]
  intro x hbx
  exact hnf x (ReflTransGen.tail hab hbx) hbx


/-- Any semi-complete relation `r` is inductive. -/
lemma rel_inductive_of_semi_complete: semi_complete r → rel_inductive r := by
  rintro ⟨un, wn⟩
  intro N f hf
  have ⟨a, ha⟩ := wn (f 0)

  use a
  intro b hb
  obtain ⟨n, hn⟩ := hb
  obtain ⟨nf, hnf⟩ := wn (f n)
  suffices ∃nf, r∗ b nf ∧ a = nf by
    · cases this; simp_all

  use nf, hn.right ▸ hnf.right
  apply un a nf ⟨ha.left, hnf.left⟩

  have haf₀: (r≡) a (f 0) := EqvGen.symm _ _ (ha.right.to_equiv)
  have hf₀fₙ: (r≡) (f 0) (f n) :=
    ReflTransGen.to_equiv <| hf.reflTrans 0 n hn.left <| Nat.zero_le n

  have hfₙnf: (r≡) (f n) nf := hnf.right.to_equiv
  apply EqvGen.trans _ _ _ haf₀
  apply EqvGen.trans _ _ _ hf₀fₙ hfₙnf


/-- Any confluent relation `r` has the normal form property. -/
lemma nf_of_confluent: confluent r → normal_form_property r := by
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

/--
Any relation with the normal form property has the _unique_ normal form
property.
-/
lemma unf_of_nf: normal_form_property r → unique_normal_form_property r := by
  intro hnf a b ⟨hnfa, hnfb⟩ hequiv
  have := hnf a b hnfb hequiv
  cases this.cases_head
  · assumption
  · exfalso; apply hnfa; tauto

/-- Any semi-complete relation is confluent. -/
lemma confluent_of_semi_complete: semi_complete r → confluent r := by
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

/-- Any inductive and increasing relation is strongly normalizing. -/
lemma strongly_normalizing_of_inductive_of_increasing:
    rel_inductive r → increasing r → strongly_normalizing r := by
  intro hInd hInc
  by_contra! h

  obtain ⟨seq, hseq⟩ := h
  have hseq': reduction_seq r ⊤ seq := by simpa using hseq
  obtain ⟨f, hf⟩ := increasing_trans_of_increasing hInc
  obtain ⟨a, ha⟩ := hInd hseq'
  simp at ha hseq

  have ha': ∀n, r∗ (seq n) a := fun n ↦ ha n

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
               _ = f (seq n) - f (seq n) + f (seq (n + 1)) := by omega
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

example (a b c: α) (hr₁: r∗ a b) (hr₂: r⁺ b c): r⁺ a c := by
  exact TransGen.trans_right hr₁ hr₂


/-- Any subcommutative relation is confluent. -/
lemma confluent_of_subcommutative: subcommutative r → confluent r := by
  intro hsc
  unfold subcommutative at hsc
  apply semi_confluent_iff_confluent.mp
  rintro a b c ⟨hab, hac⟩
  induction hab using ReflTransGen.head_induction_on generalizing c with
  | refl =>
    use c, ReflTransGen.single hac
  | @head a b' step seq ih =>
    obtain ⟨d', hd'₁, hd'₂⟩ := hsc ⟨step, hac⟩
    rcases hd'₁ with (- | h₁) <;> rcases hd'₂ with (- | h₂)
    · use b
    · use b, by rfl, ReflTransGen.head h₂ seq
    · apply ih h₁
    · obtain ⟨d, hd₁, hd₂⟩ := ih h₁
      have: r∗ c d := ReflTransGen.head h₂ hd₂
      use d

/-- A normal form is always strongly normalizing. -/
lemma strongly_normalizing_of_normal_form {a} (hnf: normal_form r a): strongly_normalizing' r a := by
  by_contra hinf
  obtain ⟨f, hf⟩ := hinf
  have: r a (f 1) := hf.1 ▸ hf.2 0 (ENat.coe_lt_top 0)
  apply hnf
  use (f 1)

end rel_properties


end Thesis
