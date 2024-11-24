import Thesis.ARS
import Thesis.BasicProperties
import Thesis.Newman

namespace Thesis

/-!

# WCR ∧ WN ∧ Inc ⇒ SN

Since this proof requires some proofs from Thesis.ARS and Thesis.Newman, it can't be in
BasicProperties along with the rest of the proofs.

-/

section wcr_wn_inc

open Relation

variable {α I: Type*} (r: Rel α α)

private lemma elem_graph_sn (A: ARS α Unit):
    strongly_normalizing' A.union_rel a → strongly_normalizing ((A.reduction_graph a).ars.union_rel) := by
  intro hsn'
  intro hsn
  obtain ⟨f, hseq⟩ := hsn

  have: (A.union_rel)∗ a (f 0) := by
    have := (f 0).prop
    simp [ARS.union_rel] at this
    exact this

  apply hsn'

  obtain ⟨N', f', hseq', heq₁, heq₂⟩ := reduction_seq.from_reflTrans this
  have := hseq'.concat _ _ _ hseq heq₂
  simp at this
  use (fun_aux N' f' (fun n ↦ f n))
  simp [fun_aux, heq₁]
  exact this


private lemma union_rel_unit (A: ARS α Unit): A.union_rel = A.rel () := by
  ext
  simp [ARS.union_rel]
  aesop

/--
If there is an infinite transitive reduction sequence of elements (aₙ) which all reduce to some
common element b, then the reduction relation cannot be increasing.
-/
lemma not_increasing_of_infinite_common_reduct (hseq: reduction_seq r⁺ ⊤ f) (hf: ∀n, r⁺ (f n) b):
    ¬increasing r := by
  intro hInc
  obtain ⟨g, hg⟩ := increasing_trans_of_increasing hInc

  -- b must have some value under g.
  let n := g b

  have hsm: StrictMono (g ∘ f) := by
    apply strictMono_nat_of_lt_succ
    intro n
    apply hg
    apply hseq

    all_goals simp only [top_add, ENat.coe_lt_top, lt_add_one]

  -- By strict monotonicity, we have n ≤ g (f n)
  have hle: n ≤ g (f n) := by
    exact hsm.le_apply

  -- But by hg and hf, we have g (f n) < n.
  have hlt: g (f n) < n := hg (hf n)

  -- Contradiction.
  absurd hle
  exact Nat.not_le_of_lt hlt

open Classical in
/--
If `a₀` is not strongly normalizing, but does reduce to some normal form nf, and r is weakly
confluent, there must be `c, d` s.t. `a₀ ->⁺ a₁ ->⁺ b ->> nf` where `a₁` is not SN.

This allows us to construct an infinite chain `a₀ →⁺ a₁ →⁺ ⋯` with `aₙ ->> nf` for all `n`.
-/
-- TODO fix the naming in the proof...
private lemma step_aux (hwcr: weakly_confluent r) (a₀ nf: α)
    (hnsn: ¬strongly_normalizing' r a₀) (hnf: normal_form r nf) (hanf: r∗ a₀ nf):
    ∃a₁ b, ¬strongly_normalizing' r a₁ ∧ r⁺ a₀ a₁ ∧ r⁺ a₁ b ∧ r∗ b nf := by
  -- There is some reduction sequence from a to nf, and there must be some first element which is
  -- SN (since nf is SN).
  obtain ⟨N, g, hseq, heq₁, heq₂⟩ := reduction_seq.from_reflTrans hanf
  have exists_sn: ∃n, n < N + 1 ∧ strongly_normalizing' r (g n) := by
    use N, by omega, heq₂ ▸ strongly_normalizing_of_normal_form r hnf

  let first_sn := Nat.find exists_sn
  -- This first SN index cannot be 0, as g 0 = a and a is not SN
  obtain ⟨last_not_sn, h⟩: ∃last_not_sn, first_sn = last_not_sn + 1 := by
    suffices: first_sn ≠ 0
    · use first_sn - 1
      omega
    intro hzero
    have := Nat.find_spec exists_sn
    simp_rw [first_sn] at hzero
    rw [hzero, heq₁] at this
    itauto

  have hN: first_sn < N + 1 := by
    apply (Nat.find_spec exists_sn).1

  have hN': last_not_sn < N + 1 := by
    omega

  -- Therefore we must have a₀ ->> a₁ -> b ->> nf with a₁ not SN
  -- There must be an infinite reduction sequence a₁ -> a₂ -> ...
  let a₁ := g last_not_sn
  let b := g (last_not_sn + 1)

  have hbsn: strongly_normalizing' r b := by
    convert (Nat.find_spec exists_sn).2
    omega

  have ha₁nsn: ¬strongly_normalizing' r a₁ := by
    have := Nat.find_min (m := last_not_sn) exists_sn (by omega)
    simp only [not_and] at this
    apply this
    omega

  simp only [not_not, strongly_normalizing'] at ha₁nsn
  obtain ⟨f', hf'⟩ := ha₁nsn
  simp at hf'

  let a₂ := f' 1

  have ha₂nsn: ¬strongly_normalizing' r a₂ := by
    simp only [not_not, strongly_normalizing']
    use (fun n ↦ f' (n + 1)), rfl
    intro n
    simpa using hf'.2 (n + 1)

  use a₂

  -- Since a₁ -> a₂ and a₁ -> b, and r is WCR, there exists some c s.t. a₂ ->> c and b ->> c.
  obtain ⟨c, ha₂c, hbc⟩: ∃c, r∗ a₂ c ∧ r∗ b c := by
    apply hwcr (a := a₁)
    constructor
    · simp_rw [<-hf'.1, a₂]
      apply hf'.2
    · simp_rw [a₁, b]
      apply hseq
      norm_cast
      omega

  -- since b ->> c, and b is SN, c must be SN
  have hcsn: strongly_normalizing' r c := by
    by_contra h
    obtain ⟨f, hstart, hseq⟩ := h
    apply hbsn

    obtain ⟨N', f', seqbc, seqbstart, seqcend⟩ := reduction_seq.from_reflTrans hbc

    have := reduction_seq.concat r N' ⊤ seqbc hseq (by rw [hstart, seqcend])
    use (fun_aux N' f' f), ?_, this
    simp [fun_aux, seqbstart]

  -- c cannot be a₂ as a₂ is not SN
  have hcnea₂: c ≠ a₂ := by
    rintro rfl
    contradiction

  have ha₂c': r⁺ a₂ c :=
    (reflTransGen_iff_eq_or_transGen.mp ha₂c).resolve_left hcnea₂

  -- Because b is SN and WCR, b is CR
  let A: ARS α Unit := { rel := fun _ ↦ r }

  have hbcr': confluent (A.reduction_graph b).ars.union_rel := by
    apply Newman.newman
    · apply elem_graph_sn
      simp_rw [union_rel_unit]
      exact hbsn
    · apply (A.reduction_graph b).down_wcr_union
      simp_rw [union_rel_unit]
      exact hwcr

  have hbcr: confluent' r b := by
    rintro c₁ c₂ ⟨hbc₁, hbc₂⟩
    have h₁: (A.reduction_graph b).ars.union_rel∗ ⟨b, by simp; rfl⟩ ⟨c₁, by simp [union_rel_unit, hbc₁]⟩ := by
      simp [SubARS.star_restrict_union]
      simp [union_rel_unit, hbc₁]

    have h₂: (A.reduction_graph b).ars.union_rel∗ ⟨b, by simp; rfl⟩ ⟨c₂, by simp [union_rel_unit, hbc₂]⟩ := by
      simp [SubARS.star_restrict_union]
      simp [union_rel_unit, hbc₂]

    have := hbcr' ⟨h₁, h₂⟩
    simp_rw [SubARS.star_restrict_union, union_rel_unit] at this
    clear * -this
    aesop

  have: r∗ b nf := by
    simp_rw [b, <-heq₂]
    apply hseq.reflTrans
    norm_cast; omega
    omega

  have hcnf: r∗ c nf := by
    obtain ⟨d, hd₁, hd₂⟩ := hbcr ⟨hbc, this⟩
    have: nf = d := by
      cases hd₂ using ReflTransGen.head_induction_on
      · rfl
      · simp [normal_form] at hnf
        exfalso
        apply hnf
        itauto
    rw [this]
    exact hd₁

  have ha₀a₂: r⁺ a₀ a₂ := by
    apply TransGen.trans_right (b := a₁)
    · simp_rw [<-heq₁, a₁]
      apply hseq.reflTrans
      norm_cast
      omega
    · simp_rw [a₂, <-hf'.1]
      apply TransGen.single
      apply hf'.2


  use c, ha₂nsn, ha₀a₂, ha₂c', hcnf


/-- Any relation which is WCR, WN, and Inc is SN. -/
lemma sn_of_wcr_wn_inc (hwcr: weakly_confluent r) (hwn: weakly_normalizing r) (hInc: increasing r): strongly_normalizing r := by
  by_contra hsn

  -- If r is not strongly normalizing, there must be an infinite reduction sequence described by f.
  obtain ⟨f, hf⟩ := hsn

  -- f 0 is not strongly normalizing
  have hnsn: ¬strongly_normalizing' r (f 0) := by
    simp only [not_not]
    use f

  -- But since r is weakly normalizing, (f 0) must reduce to some normal form.
  obtain ⟨nf, hnf, hseq⟩ := hwn (f 0)

  -- There must be at least one step from (f 0) to nf, since (f 0) is not SN, unlike nf.
  have hseq': r⁺ (f 0) nf := by
    apply ((reflTransGen_iff_eq_or_transGen.mp) hseq).resolve_left
    intro heq
    have := strongly_normalizing_of_normal_form _ hnf
    subst heq
    contradiction

  -- Using these facts, we can generate an infinite reduction sequence
  -- consisting of elements reducing to nf, which contradicts that r is increasing.
  choose! f_c f_d h using (step_aux r hwcr · nf · hnf)

  let f' := (f_c^[·] (f 0))

  have: ∀n, ¬strongly_normalizing' r (f' n) ∧ r⁺ (f' n) nf ∧ r⁺ (f' n) (f' (n + 1)) := by
    intro n
    induction n with
    | zero =>
      simp [Function.iterate_zero, id, f', hnsn, not_false_eq_true, hseq', and_true]
      obtain ⟨-, ha₀a₁, -, -⟩ := h (f 0) hnsn hseq
      exact ha₀a₁
    | succ n ih =>
      obtain ⟨hsn, -, ha₁b, hbnf⟩ := h _ ih.1 ih.2.1.to_reflTransGen
      have hnf: r⁺ (f_c (f' n)) nf := by
        apply TransGen.trans_left
        · exact ha₁b
        · exact hbnf

      and_intros
      · simp only [f', Function.iterate_succ', Function.comp]
        use hsn
      · simp only [f', Function.iterate_succ', Function.comp]
        exact hnf
      · have := h (f_c (f' n)) hsn hnf.to_reflTransGen
        simp_rw [f', Function.iterate_succ', Function.comp]
        exact this.2.1

  have hseq: reduction_seq r⁺ ⊤ f' :=
    fun n _ ↦ (this n).2.2

  have hreduct: ∀n, r⁺ (f' n) nf :=
    fun n ↦ (this n).2.1

  have hnotInc := not_increasing_of_infinite_common_reduct r hseq hreduct
  apply hnotInc hInc


end wcr_wn_inc

end Thesis
