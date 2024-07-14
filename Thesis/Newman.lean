/-
Newman.lean - two proofs of Newman's Lemma.

We start with Barendregt's proof of Newman's lemma, which makes use of the notion
of an ambiguous element, which always has an ambiguous successor if r is
weakly normalizing and weakly confluent. This contradicts strong normalization.
Therefore, a relation which is strongly normalizing and weakly confluent
cannot have ambiguous elements, hence it must be confluent.

The second proof makes use of a number of more complicated constructs.
-/
import Thesis.RelProps
import Thesis.SymmSeq

namespace Thesis

open Relation
open Classical

section newman_barendregt

variable {α} (r: Rel α α)

/-- An ambiguous element `a` has at least two distinct normal forms. -/
def ambiguous (a: α) := ∃(b c: α), normal_form r b ∧ normal_form r c ∧ (b ≠ c) ∧ (r∗ a b ∧ r∗ a c)

/-- Uniqueness of normal forms + weak normalization implies confluence. -/
def unr_wn_imp_confluence {r: Rel α α} (hwn: weakly_normalizing r) (hu: UNr_prop r): confluent r := by
  rintro a b c ⟨hab, hac⟩

  obtain ⟨d₁, hd₁⟩ := hwn b
  obtain ⟨d₂, hd₂⟩ := hwn c

  have had₁: r∗ a d₁ := ReflTransGen.trans hab hd₁.right
  have had₂: r∗ a d₂ := ReflTransGen.trans hac hd₂.right

  have hdeq: d₁ = d₂ := by apply hu; tauto; use a

  use d₁, hd₁.right
  rw [hdeq]
  exact hd₂.right

/--
In the context of Newman's lemma, an ambiguous element `a` always has a one-step
reduct which is also ambiguous (leading to an infinite sequence).
-/
def newman_ambiguous_step {r: Rel α α} (hwn: weakly_normalizing r) (hwc: weakly_confluent r) (a: α):
  ambiguous r a → ∃b, r a b ∧ ambiguous r b := by
    intro ha
    unfold ambiguous at ha
    obtain ⟨d₁, d₂, ⟨hnf₁, hnf₂, hne, hpath₁, hpath₂⟩⟩ := ha

    cases hpath₁.cases_head <;> cases hpath₂.cases_head
    · cc
    · have hnnf₁: ¬normal_form r d₁ := by
        simp [normal_form]
        rename_i h₁ h₂
        obtain ⟨x, hx, -⟩ := h₂
        rw [h₁] at hx
        use x
      contradiction
    · have hnnf₂: ¬normal_form r d₂ := by
        simp [normal_form]
        rename_i h₁ h₂
        obtain ⟨x, hx, -⟩ := h₁
        rw [h₂] at hx
        use x
      contradiction

    rename_i hb hc
    obtain ⟨b, hb⟩ := hb
    obtain ⟨c, hc⟩ := hc
    obtain ⟨d, hd⟩ := hwc a b c (by tauto)

    obtain ⟨nfd, hnfd⟩ := hwn d

    wlog h: (nfd ≠ d₁) generalizing b c d₁ d₂
    · have h': nfd ≠ d₂ := by cc
      have := this d₂ d₁ hnf₂ hnf₁ (by cc) hpath₂ hpath₁ c hc b hb (by tauto) h'
      assumption

    use b, hb.left, nfd, d₁, hnfd.1, hnf₁, h, Trans.trans (hd.1) (hnfd.2), hb.2


/-- Newman's lemma: strong normalization + local confluence implies confluence. -/
def newman (hsn: strongly_normalizing r) (hwc: weakly_confluent r): confluent r := by
  have hwn: weakly_normalizing r := strongly_normalizing_imp_weakly_normalizing hsn
  suffices hun: UNr_prop r from unr_wn_imp_confluence hwn hun
  contrapose hsn with hun
  simp only [UNr_prop, not_forall] at hun

  obtain ⟨d₁, d₂, ⟨⟨hnf₁, hnf₂⟩, ⟨a, hpath₁, hpath₂⟩, hne⟩⟩ := hun

  choose! f h₁ h₂ using (newman_ambiguous_step hwn hwc)
  have h₃: ∀N, ambiguous r (f^[N] a) := Function.Iterate.rec _ h₂ (by use d₁, d₂)

  simp [strongly_normalizing]
  use (f^[·] a)
  intro n
  rw [Function.iterate_succ', Function.comp]
  apply h₁ _ (h₃ n)

end newman_barendregt

-- prerequisites for different proof of Newman's Lemma

/- The transitive closure of `r.inv` is a strict order if `r` is SN. -/
section strict_order_trans_inv

variable {α} {r: Rel α α}

/-- A transitive step can be decomposed into a small step and, potentially, a remaining transitive step. -/
lemma small_step: r⁺ a b → ∃c, r a c ∧ (c = b ∨ r⁺ c b) := by
  intro hr
  induction hr using TransGen.head_induction_on with
  | base h => use b, h; left; rfl
  | ih h₁ h₂ _ih =>
    rename_i a c
    use c, h₁; right; exact h₂

/-- Given an infinite sequence of transitive steps, there is always a next small step. -/
lemma step (f: ℕ → α) (hf: inf_reduction_seq r⁺ f) (a: α): (∃n, r⁺ a (f n)) → (∃(p: ℕ × α), r a p.2 ∧ r⁺ p.2 (f p.1)) := by
  rintro ⟨n, hr⟩
  obtain ⟨c, hc⟩ := small_step hr
  cases hc.right with
  | inl h =>
    use (n + 1, c), hc.left
    simp [h, hf n]
  | inr h =>
    use (n, c)
    tauto

/-- The transitive closure of `r` is strongly normalizing iff `r` is strongly normalizing. -/
lemma sn_iff_sn_trans: strongly_normalizing r⁺ ↔ strongly_normalizing r := by
  unfold strongly_normalizing
  constructor
  · intro hsnt
    contrapose! hsnt with hsn
    obtain ⟨f, hf⟩ := hsn
    use f
    intro n
    exact TransGen.single (hf n)
  · intro hsn
    contrapose! hsn with hsnt
    obtain ⟨f, hf⟩ := hsnt
    have hstep := step f hf

    let f': α → α := fun x ↦ if h: ∃n, r⁺ x (f n) then (choose (hstep x h)).2 else x

    have h₁ : ∀a, (∃n, r⁺ a (f n)) → (∃n, r⁺ (f' a) (f n)) := by
      rintro a h
      have := choose_spec (hstep a h)
      simp [f', dif_pos h]
      obtain ⟨-, right⟩ := this
      exact Exists.intro (choose (hstep a h)).1 right

    have h₂ : ∀a, (∃n, r⁺ a (f n)) → r a (f' a) := by
      intro a h
      have := choose_spec (hstep a h)
      simp [f', dif_pos h]
      tauto

    have : ∀N, ∃n, r⁺ (f'^[N] (f 0)) (f n) := Function.Iterate.rec _ h₁ (Exists.intro 1 (hf 0))

    use (f'^[·] (f 0))
    simp only [inf_reduction_seq]
    intro n
    rw [Function.iterate_succ', Function.comp]
    exact h₂ _ (this n)

/-- If `r` is strongly normalizing, the transitive closure of `r.inv` is a strict order. -/
instance sn_imp_trans_strict_order [hsn: IsStronglyNormalizing r] : IsStrictOrder α (r.inv)⁺ where
  irrefl := by
    obtain ⟨hsn⟩ := hsn
    rw [<-sn_iff_sn_trans] at hsn
    contrapose! hsn
    obtain ⟨a, ha⟩ := hsn
    intro h
    apply h (fun _ ↦ a)
    simp only [forall_const]
    exact transGen_swap.mp ha

#check Function.swap_def
#check TransGen.swap
#check Function.flip_def

/-- If `r` is strongly normalizing, the transitive closure of `r.inv` is well-founded. -/
instance sn_imp_wf_trans_inv [hsn: IsStronglyNormalizing r]: IsWellFounded α (r.inv)⁺ where
  wf := by
    apply sn_imp_wf_inv
    -- this flip/swap nonsense is a bit silly...
    simp only [Rel.inv, Function.flip_def]
    nth_rw 2 [<-Function.swap_def]
    simp only [transGen_swap]
    eta_reduce
    exact sn_iff_sn_trans.mpr hsn.sn

end strict_order_trans_inv

variable {r: Rel α α}

lemma newman₂' [IsStronglyNormalizing r] (hwc: weakly_confluent r) [IsStrictOrder α (r.inv)⁺] [IsWellFounded α (r.inv)⁺]:
  confluent r := by
    sorry


lemma newman₂ [IsStronglyNormalizing r] (hwc: weakly_confluent r): confluent r := by
  exact newman₂' hwc




end Thesis
