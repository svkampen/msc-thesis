import Thesis.ReductionSeq
import Thesis.ARS
import Thesis.RelProps
import Thesis.InfReductionSeq
import Mathlib.Logic.Relation

namespace Thesis

section

variable {α I}
variable (A: ARS α I) (a: α)
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

/--
An ARS has the component-wise cofinality property (CP_conv) if for every a ∈ A,
there exists a reduction a = b₀ → b₁ → ⋯ that is cofinal in A|{b | a ≡ b}.
-/
def cofinality_property_conv :=
  ∀a, ∃N f, ∃(hseq: reduction_seq (A.component a).ars.union_rel N f),
    cofinal_reduction hseq ∧ hseq.start = a

/-- Any ARS with the cofinality property is confluent. -/
lemma cp_imp_cr {A: ARS α I}: cofinality_property A → confluent A.union_rel := by
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
    have := this hac hab nc hnc hcsc nb hnb hbsb (le_of_lt hle)
    tauto

  have hbsc := hbsb.trans <| hseq.star nb nc hnc hle

  use (f nc)
  simp [S.star_restrict_union] at hcsc hbsc
  exact ⟨hbsc, hcsc⟩


-- A cofinal reduction sequence w.r.t. the reduction graph of a is also
-- cofinal w.r.t. the component of a. That means CP ↔ CP_conv.
lemma cp_iff_cp_conv : cofinality_property A ↔ cofinality_property_conv A := by
  constructor
  · show cofinality_property A → cofinality_property_conv A
    intro hcp a
    have hc: conv_confluent A.union_rel :=
      conv_confluent_iff_confluent.mpr (cp_imp_cr hcp)

    obtain ⟨N, f, hseq, hcr, hstart⟩ := hcp a

    have heq: (A.reduction_graph a).p = (A.union_rel∗ a ·) := A.reduction_graph_p

    let f' : ℕ → { b // A.conv a b } :=
      fun n ↦ let ⟨val, prop⟩ := f n; ⟨val, (heq ▸ prop).to_equiv⟩

    use N, f', hseq
    constructor
    · rintro ⟨a', ha'⟩
      have ⟨d, hd₁, hd₂⟩ := hc ha'
      obtain ⟨⟨b, hb⟩, ⟨n, hb₁⟩, hb₂⟩ := hcr ⟨d, heq ▸ hd₁⟩
      use ⟨b, (heq ▸ hb).to_equiv⟩
      constructor
      · use n
        simp_all only [f', and_imp, true_and]
      · simp only [SubARS.star_restrict_union] at hb₂ hd₂ ⊢
        trans d <;> simp only [hb₂, hd₂]
    · simpa [f'] using hstart
  · show cofinality_property_conv A → cofinality_property A
    intro hcp' a

    obtain ⟨N, f, hseq, hcr, hstart⟩ := hcp' a
    have hstar := hseq.star 0

    simp only [reduction_seq.start, zero_le, true_implies, SubARS.star_restrict_union] at hstart hstar
    rw [hstart] at hstar

    have heq: (A.reduction_graph a).p = (A.union_rel∗ a ·) := A.reduction_graph_p

    let f': ℕ → { b // (A.reduction_graph a).p b } :=
      fun (n: ℕ) ↦
        if h: (n < N + 1)
          then ⟨f n, heq ▸ hstar _ h⟩
          else ⟨f 0, heq ▸ hstar _ (by simp)⟩

    have hseq' : reduction_seq (A.reduction_graph a).ars.union_rel N f' := by
      intro n hn
      have hn₁: n < N + 1 := lt_of_lt_of_le hn le_self_add
      have hn₂: n + 1 < N + 1 := (WithTop.add_lt_add_iff_right WithTop.one_ne_top).mpr hn
      convert hseq n hn using 0
      simp [f', dif_pos hn₁, dif_pos hn₂, reduction_seq, SubARS.restrict_union]

    use N, f', hseq'
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨⟨b, hbconv⟩, ⟨n, hn₁, hn₂⟩, hb₂⟩ := hcr ⟨c, (heq ▸ hc).to_equiv⟩
      simp [reduction_seq.elems, f', SubARS.star_restrict_union] at hb₂ ⊢
      use n
      simp_all only [heq, Set.mem_setOf_eq, dite_true, and_self]
    · simp [hstart, f']

lemma cofinality_property.to_conv: cofinality_property A → cofinality_property_conv A
  := (cp_iff_cp_conv A).mp

noncomputable section countable_confluent_imp_cp

/-- The sequence bₙ as defined in Klop (1980). -/
private def cnt_cr_imp_cp_aux {A: ARS α I} {S : SubARS A} (f : ℕ → S.Subtype) (a' : S.Subtype)
  (common_reduct : ∀ (x y : S.Subtype), ∃ c, S.ars.union_rel∗ x c ∧ S.ars.union_rel∗ y c)
| 0 => a'
| n + 1 => Classical.choose (common_reduct (cnt_cr_imp_cp_aux f a' common_reduct n) (f n))

/--
A countable, confluent ARS has the cofinality property.
-/
lemma cnt_cr_imp_cp [cnt: Countable α] (cr: confluent A.union_rel): cofinality_property A := by
  intro a
  set S := A.reduction_graph a with S_def
  set β := {b // S.p b} with β_def

  -- a is in its own reduction graph
  let a': β := ⟨a, by simp [S_def]; rfl⟩

  -- G(a) must also be countable
  have cnt': Countable β := Subtype.countable
  have hne: Nonempty β := ⟨a'⟩

  -- and, since it is nonempty, must have a surjective function ℕ → β
  obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp cnt'


  -- every pair of elements in β must have a common reduct, by confluence
  have common_reduct (x y: β): ∃c, S.ars.union_rel∗ x c ∧ S.ars.union_rel∗ y c := by
    apply S.down_confluent_union A cr (a := a')
    constructor
    · have := x.prop
      simp_all [S.star_restrict_union]
    · have := y.prop
      simp_all [S.star_restrict_union]

  -- we can form a sequence of common reducts of aₙ
  let f' := cnt_cr_imp_cp_aux f a' common_reduct

  -- this is a S.union_rel∗-reduction sequence
  have hf': reduction_seq S.ars.union_rel∗ ⊤ f' := by
    intro n _
    simp [f']
    have := Classical.choose_spec (common_reduct (f' n) (f n))
    exact this.1

  -- with a corresponding regular reduction sequence
  obtain ⟨N, g, hg⟩ := InfReductionSeq.rt_seq_imp_regular_seq f' hf'

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
        · simp
        · norm_cast at hm ⊢
          omega
      · rfl
    · rw [<-heq, <-hn]
      have := Classical.choose_spec (common_reduct (f' n) (f n))
      simp [f']
      exact this.2
  · simp [reduction_seq.start]
    rw [<-hg.2.2]
    simp [f', cnt_cr_imp_cp_aux]


end countable_confluent_imp_cp

/-
We will occasionally need an acyclic cofinal reduction sequence. Luckily,
any cofinal reduction sequence that contains cycles can be made acyclic.

We can distinguish three basic types of cofinal reduction sequence:

- Finite; in this case, the last element of the reduction sequence on its own
  forms a cofinal reduction sequence, and since it consists of a single element,
  it is obviously acyclic.
- Infinite, with at least one element appearing infinitely often. In this case,
  the element appearing infinitely often on its own forms a cofinal reduction
  sequence, which again is obviously acyclic.
- Infinite, with each element appearing only finitely often. In this case, we
  will want to skip over any potential cycles, by using only the last appearance
  of an element.

We will handle each of these cases in sequence, and then end with a lemma
stating that any cyclic cofinal reduction sequence has an acyclic counterpart.
-/

section cyclic_finite

variable {r: Rel α α} {f: ℕ → α} {N: ℕ} (hseq: reduction_seq r N f)

/--
The acyclic version of a finite cofinal reduction sequence is simply the
last element of that reduction sequence.
-/
def acyclic_of_finite :=
  reduction_seq.refl r (fun n ↦ hseq.end)

lemma acyclic_of_finite.is_cofinal (hcf: cofinal_reduction hseq):
    cofinal_reduction <| acyclic_of_finite hseq := by
  intro a
  obtain ⟨b, ⟨n, hmem, heq⟩, hb⟩ := hcf a
  simp [acyclic_of_finite]
  norm_cast at hmem
  simp at hmem
  by_cases heqₙ: n = N
  · subst heqₙ heq
    assumption
  · trans b
    · exact hb
    subst heq
    apply_mod_cast hseq.star
    all_goals omega

def reduction_seq.acyclic (hseq: reduction_seq r N' f) := ∀(n m: ℕ), n < N' → m < N' → f n = f m → n = m

lemma acyclic_of_finite.is_acyclic: (acyclic_of_finite hseq).acyclic := by
  simp [acyclic_of_finite, reduction_seq.acyclic]

end cyclic_finite

section cyclic_infinite

variable (f: ℕ → α) (hseq: reduction_seq r ⊤ f) (hcycle: ¬hseq.acyclic)
  (hcf: cofinal_reduction hseq)

/--
If `h: appears_infinitely f n`, the element `f n` appears infinitely often.
-/
def appears_infinitely (n: ℕ) := ∀N, ∃m > N, f n = f m

/--
If `h: appears_finitely f n`, the element `f n` appears finitely often.
-/
def appears_finitely (n: ℕ):= ∃N, ∀m > N, f n ≠ f m

/-- A stronger version of `appears_finitely` which gives us the final appearance. -/
def appears_finitely' (n: ℕ) := ∃N, f n = f N ∧ ∀m > N, f n ≠ f m

open Classical in
private lemma aux: appears_finitely f n → appears_finitely' f n := by
  rintro hla
  use Nat.find hla
  constructor
  · have: Nat.find hla ≥ n := by
      by_contra h
      simp at h
      obtain ⟨x, hx₁, hx₂⟩ := h
      apply hx₂ n hx₁
      rfl
    by_cases h: Nat.find hla = n
    · rw [h]
    · have: Nat.find hla > n := by omega
      by_contra h
      have: Nat.find hla > (Nat.find hla) - 1 := by omega
      have := Nat.find_min hla this
      simp at this
      obtain ⟨m, hmlt, hmeq⟩ := this
      have: m = Nat.find hla ∨ Nat.find hla < m := by omega
      rcases this with (heq | hlt)
      · apply h
        cc
      · apply (Nat.find_spec hla m hlt hmeq)
  · exact Nat.find_spec hla

lemma no_appears_infinitely_imp_appears_finitely: (¬∃n, appears_infinitely f n) ↔ ∀n, appears_finitely f n := by
  simp [appears_infinitely, appears_finitely]

noncomputable def acyclic_of_appears_infinitely
    (hinf: ∃n, appears_infinitely f n) :=
  reduction_seq.refl r (fun n ↦ f <| hinf.choose)

include hcf in
lemma acyclic_of_appears_infinitely.reduction_seq (hinf: ∃n, appears_infinitely f n):
    cofinal_reduction <| acyclic_of_appears_infinitely r f hinf := by
  intro a
  obtain ⟨b, ⟨n, -, heq⟩, hab⟩ := hcf a
  obtain hm := hinf.choose_spec
  set m := hinf.choose with m_def

  have := hseq.star
  simp [acyclic_of_appears_infinitely]
  trans b
  use hab
  rw [<-heq]

  obtain ⟨n₂, hn₂⟩ := hm n
  have := hseq.star n n₂
  simp at this
  rw [<-m_def, hn₂.2]
  apply this
  omega

section all_appear_finitely

variable (hf: ∀n, appears_finitely' f n)

noncomputable def f_idxs (n: ℕ): ℕ :=
  (hf (if n = 0 then n else (f_idxs (n - 1)) + 1)).choose

noncomputable def f' (n: ℕ) :=
  f <| f_idxs f hf n

include hseq in
lemma hseq': reduction_seq r ⊤ (f' f hf) := by
  intro n hn
  dsimp [f']
  nth_rw 2 [f_idxs]

  have ⟨heq, hneq⟩ := (hf ((f_idxs f hf n) + 1)).choose_spec

  simp only [<-heq, ENat.coe_lt_top, hseq]

lemma arg_le_hf (n: ℕ): n ≤ (hf n).choose := by
  have ⟨heq, hneq⟩ := (hf n).choose_spec
  by_contra! h
  apply hneq n h rfl

lemma f_idxs.strictMono: StrictMono (f_idxs f hf) := by
  apply strictMono_nat_of_lt_succ
  intro n
  nth_rw 2 [f_idxs]
  have := arg_le_hf f hf ((f_idxs f hf n) + 1)
  omega


include hcf in
lemma hseq'.cofinal: cofinal_reduction (hseq' r f hseq hf) := by
  intro a
  obtain ⟨b, ⟨n, -, heq⟩, hab⟩ := hcf a

  simp only [reduction_seq.elems, top_add, ENat.coe_lt_top, Set.setOf_true, Set.image_univ,
    Set.mem_range, exists_exists_eq_and]

  use n
  rw [f']
  have hge: f_idxs f hf n ≥ n := (f_idxs.strictMono f hf).le_apply
  trans b
  · assumption
  · rw [<-heq]
    apply hseq.star _ _ _ hge
    simp only [top_add, ENat.coe_lt_top]

/--
`f_idxs f hf n` represents the greatest index of an element of f. Hence, if
`m > f_idxs f hf n`, `f (f_idxs f hf n) ≠ f m`.
-/
lemma f_idxs_last {n m: ℕ} (hm: m > f_idxs f hf n): f (f_idxs f hf n) ≠ f m := by
  rw [f_idxs] at *
  have ⟨heq, hneq⟩:= (hf (if n = 0 then n else f_idxs f hf (n - 1) + 1)).choose_spec
  rw [<-heq]
  apply hneq _ hm

lemma hseq'.acyclic: (hseq' r f hseq hf).acyclic := by
  simp [reduction_seq.acyclic]
  rintro n m heq
  simp [f'] at heq
  by_contra h
  wlog h: n < m generalizing n m
  · apply this m n heq.symm (by tauto) (by omega)

  apply f_idxs_last f hf (f_idxs.strictMono f hf h) heq


end all_appear_finitely

end cyclic_infinite

section cyclic

variable {r: Rel α α}

/-- Any (cyclic) cofinal reduction sequence has an acyclic counterpart. -/
lemma cofinal_reduction_acyclic (hseq: reduction_seq r N f) (hcf: cofinal_reduction hseq):
    ∃(N': _) (f': _) (hseq': reduction_seq r N' f'), cofinal_reduction hseq' ∧ hseq'.acyclic := by
  cases N
  -- If the cofinal reduction sequence is finite, the last element on its own
  -- forms a cofinal reduction sequence which is acyclic.
  case coe N =>
    apply Exists.intro
    apply Exists.intro
    use acyclic_of_finite hseq,
        acyclic_of_finite.is_cofinal hseq hcf,
        acyclic_of_finite.is_acyclic hseq

  -- If the cofinal reduction sequence is infinite...
  case top =>
    by_cases hinf: ∃n, appears_infinitely f n
    -- ...and at least one element appears infinitely often, that element on
    -- its own forms a cofinal reduction sequence which is acyclic.
    · apply Exists.intro
      apply Exists.intro
      use (acyclic_of_appears_infinitely r f hinf)
      constructor
      exact acyclic_of_appears_infinitely.reduction_seq r f hseq hcf hinf
      simp [reduction_seq.acyclic]
    -- ...and all elements appear only finitely often, we are in the complicated
    -- case, where we have to construct a new infinite reduction sequence which
    -- skips all of the cycles.
    · have := (no_appears_infinitely_imp_appears_finitely f).mp hinf
      have: ∀n, appears_finitely' f n := fun n ↦ aux _ (this n)
      apply Exists.intro
      apply Exists.intro
      use (hseq' r f hseq this)
      constructor
      · apply hseq'.cofinal _ _ _ hcf
      · apply hseq'.acyclic _ _ hseq





end cyclic

end

end Thesis
