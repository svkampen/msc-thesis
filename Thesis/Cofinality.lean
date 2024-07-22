import Thesis.ReductionSeq
import Thesis.ARS
import Thesis.RelProps

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

def cofinality_property :=
  ∀a, ∃N f, ∃(hseq: reduction_seq (A.reduction_graph a).ars.union_rel N f), cofinal_reduction hseq ∧ hseq.start = a


/-- Any ARS with the cofinality property is confluent. -/
lemma cp_imp_cr: cofinality_property A → confluent A.union_rel := by
  intro hcp
  rintro a b c ⟨hab, hac⟩

  have hcp_a := hcp a
  set S := A.reduction_graph a with S_def
  obtain ⟨N, f, hseq, hcf, hstart⟩ := hcp_a

  obtain ⟨sb, ⟨hsb, hbsb⟩⟩ := hcf ⟨b, hab⟩
  obtain ⟨sc, ⟨hsc, hcsc⟩⟩ := hcf ⟨c, hac⟩

  simp [reduction_seq.elems] at hsc hsb

  obtain ⟨nb, hnb, rfl⟩ := hsb
  obtain ⟨nc, hnc, rfl⟩ := hsc

  wlog hle: nb ≤ nc generalizing nb nc hbsb hcsc b hab c hac
  · simp at hle
    have := this c b hac hab nc hnc hcsc nb hnb hbsb (le_of_lt hle)
    tauto

  have hbsc := hbsb.trans <| hseq.star nb nc hnc hle

  use (f nc)
  simp [S.star_restrict] at hcsc hbsc
  exact ⟨hbsc, hcsc⟩

noncomputable section countable_confluent_imp_cp

def f' {α : Type*} {I : Type*} (A : ARS α I) (a : α)
  (S : SubARS A (fun b' ↦ A.union_rel∗ a b') Unit) (f : ℕ → { b // S.prop b }) (a' : { b // S.prop b })
  (common_reduct : ∀ (x y : { b // S.prop b }), ∃ c, S.ars.union_rel∗ x c ∧ S.ars.union_rel∗ y c)
| 0 => a'
| n + 1 => Classical.choose (common_reduct (f' A a S f a' common_reduct n) (f n))

/--
An axiom that is "obvious" when written down in a pen-and-paper proof, but which
is unfortunately really difficult to prove in Lean:

If we have an infinite reflexive-transitive reduction sequence
a0 ->* a1 ->* a2 ...
there must be some (finite or infinite) reduction sequence
a0 -> ... -> a1 -> ... -> a2 -> ...
-/
axiom exists_regular_seq: ∀f, reduction_seq r∗ ⊤ f → ∃f' N, reduction_seq r N f' ∧ (∀n, ∃m: ℕ, ∃(hm: m < N + 1), f n = f' m) ∧ f 0 = f' 0

/--
A countable, confluent ARS has the cofinality property.
-/
lemma cnt_cr_imp_cp [cnt: Countable α] (cr: confluent A.union_rel): cofinality_property A := by
  intro a
  set S := A.reduction_graph a with S_def
  set β := {b // S.prop b} with β_def

  have cnt': Countable β := Subtype.countable
  have hne: Nonempty β := by
    use a
    simp
    rfl

  obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp cnt'

  let a': β := ⟨a, by simp; rfl⟩

  have common_reduct (x y: β): ∃c, S.ars.union_rel∗ x c ∧ S.ars.union_rel∗ y c := by
    apply S.down_confluent A cr a'
    constructor
    · have := x.prop
      simp_all [S.star_restrict]
    · have := y.prop
      simp_all [S.star_restrict]

  let f'' := f' A a S f a' common_reduct

  have hf': reduction_seq S.ars.union_rel∗ ⊤ f'' := by
    intro n _
    simp [f'', f']
    have := Classical.choose_spec (common_reduct (f'' n) (f n))
    exact this.1

  obtain ⟨g, N, hg⟩ := exists_regular_seq S.ars.union_rel f'' hf'

  use N, g, hg.1
  constructor
  · intro x
    obtain ⟨n, hn⟩ := hf x
    obtain ⟨m, hm, heq⟩ := hg.2.1 (n + 1)
    use (g m)
    simp [reduction_seq.elems]
    constructor
    · use m
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
