import Thesis.ReductionSeq
import Thesis.ARS
import Thesis.RelProps
import Thesis.InfReductionSeq
import Mathlib.Logic.Relation

namespace Thesis

section

variable {α I}
variable (A: ARS α I) (a: α) [Nonempty α]
variable (r: α → α → Prop)

/--
A set `s` is cofinal in r if every element `a: α` reduces to
some b in the set.
-/
def cofinal (s: Set α) := ∀a, ∃b ∈ s, r∗ a b

/--
A reduction sequence is cofinal in r if the set of all elements in the sequence
is cofinal in r.
-/
def cofinal_reduction {r: Rel α α} {N: ℕ∞} {f: ℕ → α} (hseq: reduction_seq r N f)
  := cofinal r hseq.elems

/--
An ARS has the cofinality property (CP) if for every a ∈ A, there exists a
reduction a = b₀ → b₁ → ⋯ that is cofinal in A|{b| a →∗ b}.
-/
def cofinality_property :=
  ∀a, ∃N f, ∃(hseq: reduction_seq (A.reduction_graph a).ars.union_rel N f),
    cofinal_reduction hseq ∧ hseq.start = a


/-- Any ARS with the cofinality property is confluent. -/
lemma cp_imp_cr: cofinality_property A → confluent A.union_rel := by
  intro hcp
  rintro a b c ⟨hab, hac⟩

  have hcp_a := hcp a
  set S := A.reduction_graph a with S_def
  obtain ⟨N, f, hseq, hcf, hstart⟩ := hcp_a

  have Sprop: S.p = A.union_rel∗ a := by
    simp [S_def]

  obtain ⟨sb, ⟨hsb, hbsb⟩⟩ := hcf ⟨b, Sprop ▸ hab⟩
  obtain ⟨sc, ⟨hsc, hcsc⟩⟩ := hcf ⟨c, Sprop ▸ hac⟩

  simp [reduction_seq.elems] at hsc hsb

  obtain ⟨nb, hnb, rfl⟩ := hsb
  obtain ⟨nc, hnc, rfl⟩ := hsc

  wlog hle: nb ≤ nc generalizing nb nc hbsb hcsc b hab c hac
  · simp at hle
    have := this c b hac hab nc hnc hcsc nb hnb hbsb (le_of_lt hle)
    tauto

  have hbsc := hbsb.trans <| hseq.star nb nc hnc hle

  use (f nc)
  simp [S.star_restrict_union] at hcsc hbsc
  exact ⟨hbsc, hcsc⟩

noncomputable section countable_confluent_imp_cp

/-- The sequence bₙ as defined in Klop (1980). -/
def f' {α : Type*} {I : Type*} (A : ARS α I) (a : α)
  (S : SubARS A) (f : ℕ → { b // S.p b }) (a' : { b // S.p b })
  (common_reduct : ∀ (x y : { b // S.p b }), ∃ c, S.ars.union_rel∗ x c ∧ S.ars.union_rel∗ y c)
| 0 => a'
| n + 1 => Classical.choose (common_reduct (f' A a S f a' common_reduct n) (f n))

/--
A countable, confluent ARS has the cofinality property.
-/
lemma cnt_cr_imp_cp [cnt: Countable α] (cr: confluent A.union_rel): cofinality_property A := by
  intro a
  set S := A.reduction_graph a with S_def
  set β := {b // S.p b} with β_def

  -- G(a) must also be countable
  have cnt': Countable β := Subtype.countable
  have hne: Nonempty β := by
    use a
    simp [S_def]
    rfl

  -- and, since it is nonempty, must have a surjective function ℕ → β
  obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp cnt'

  let a': β := ⟨a, by simp [S_def]; rfl⟩

  -- every pair of elements in β must have a common reduct, by confluence
  have common_reduct (x y: β): ∃c, S.ars.union_rel∗ x c ∧ S.ars.union_rel∗ y c := by
    apply S.down_confluent_union A cr a'
    constructor
    · have := x.prop
      simp_all [S.star_restrict_union]
    · have := y.prop
      simp_all [S.star_restrict_union]

  -- we can form a sequence of common reducts of aₙ
  let f'' := f' A a S f a' common_reduct

  -- this is a S.union_rel∗-reduction sequence
  have hf': reduction_seq S.ars.union_rel∗ ⊤ f'' := by
    intro n _
    simp [f'', f']
    have := Classical.choose_spec (common_reduct (f'' n) (f n))
    exact this.1

  -- with a corresponding regular reduction sequence
  obtain ⟨N, g, hg⟩ := InfReductionSeq.rt_seq_imp_regular_seq f'' hf'

  -- and every element in β has a reduct in the sequence
  use N, g, hg.1
  constructor
  · intro x
    obtain ⟨n, hn⟩ := hf x
    obtain ⟨m, hm, heq⟩ := hg.2.1 (n + 1)
    use (g m)
    simp [reduction_seq.elems]
    constructor
    · use m
      constructor
      · cases N
        · simp; exact WithTop.coe_lt_top m
        · norm_cast at hm ⊢
          omega
      · rfl
    · rw [<-heq, <-hn]
      have := Classical.choose_spec (common_reduct (f'' n) (f n))
      simp [f'', f']
      exact this.2
  · simp [reduction_seq.start]
    rw [<-hg.2.2]
    simp [f'', f']


end countable_confluent_imp_cp

end

end Thesis
