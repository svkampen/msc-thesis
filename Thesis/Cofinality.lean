import Thesis.ARS
import Thesis.BasicProperties
import Thesis.InfReductionSeq
import Mathlib.Logic.Relation

/-!

# Cofinality, cofinal reductions, and related notions

We explore various properties related to cofinality, defining the notion of a cofinal set and
cofinal reduction, as well as the cofinality property (reduction graph and component versions).

We then prove two standard theorems about these: CP => CR and CR + countable => CP.

In later developments, we will need _acyclic_ cofinal reduction sequences. We therefore show that
any cofinal reduction sequence can be made acyclic.

-/

namespace Thesis

section

variable {α I}
variable (A: ARS α I) (a: α)
variable (r: α → α → Prop)

/--
A set `s` is cofinal in r if every element `a: α` reduces to
some b in the set.
-/
def cofinal (s: Set α) :=
  ∀a, ∃b ∈ s, r∗ a b

/--
A reduction sequence is cofinal in r if the set of all elements in the sequence
is cofinal in r.
-/
def cofinal_reduction {r: Rel α α} {N: ℕ∞} {f: ℕ → α} (hseq: reduction_seq r N f) :=
  cofinal r hseq.elems

/--
An ARS has the cofinality property (CP) if for every a ∈ A, there exists a
reduction a = b₀ → b₁ → ⋯ that is cofinal in A|{b| a →∗ b}.
-/
def cofinality_property :=
  ∀a, ∃N f, ∃(hseq: reduction_seq (A.reduction_graph a).ars.union_rel N f),
    cofinal_reduction hseq ∧ hseq.start = a

/--
An ARS has the component-wise cofinality property (CP≡) if for every a ∈ A,
there exists a reduction a = b₀ → b₁ → ⋯ that is cofinal in A|{b | a ≡ b}.
-/
def cofinality_property_conv :=
  ∀a, ∃N f, ∃(hseq: reduction_seq (A.component a).ars.union_rel N f),
    cofinal_reduction hseq ∧ hseq.start = a

/-- Any ARS with the cofinality property is confluent. -/
lemma cr_of_cp {A: ARS α I}: cofinality_property A → confluent A.union_rel := by
  intro hcp
  rintro a b c ⟨hab, hac⟩

  obtain ⟨N, f, hseq, hcf, hstart⟩ := hcp a
  obtain ⟨sb, hsb, hbsb⟩ := hcf ⟨b, by simp [hab]⟩
  obtain ⟨sc, hsc, hcsc⟩ := hcf ⟨c, by simp [hac]⟩

  simp [reduction_seq.elems] at hsc hsb

  obtain ⟨nb, hnb, rfl⟩ := hsb
  obtain ⟨nc, hnc, rfl⟩ := hsc

  wlog hle: nb ≤ nc generalizing nb nc hbsb hcsc b hab c hac
  · simp at hle
    have := this hac hab nc hnc hcsc nb hnb hbsb (le_of_lt hle)
    tauto

  have hbsc := hbsb.trans <| hseq.reflTrans nb nc hnc hle

  use (f nc)

  simp [SubARS.star_restrict_union] at hcsc hbsc
  exact ⟨hbsc, hcsc⟩


/--
The reduction-graph version of the cofinality property and the component version are equivalent.
-/
lemma cp_iff_cp_conv : cofinality_property A ↔ cofinality_property_conv A := by
  constructor
  · show cofinality_property A → cofinality_property_conv A
    intro hcp a
    have hc: conv_confluent A.union_rel :=
      conv_confluent_iff_confluent.mpr (cr_of_cp hcp)

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
    have hstar := hseq.reflTrans 0

    simp_all only [reduction_seq.start, zero_le, true_implies, SubARS.star_restrict_union]

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

/-- A countable, confluent ARS has the cofinality property. -/
lemma cp_of_countable_cr [cnt: Countable α] (cr: confluent A.union_rel):
    cofinality_property A := by
  intro a
  set S := A.reduction_graph a with S_def
  set β := {b // S.p b}

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
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    constructor
    · simpa [S_def, S.star_restrict_union] using hx
    · simpa [S_def, S.star_restrict_union] using hy


  -- we can form a sequence of common reducts of aₙ
  let f' := cnt_cr_imp_cp_aux f a' common_reduct

  -- this is a S.union_rel∗-reduction sequence
  have hf': reduction_seq S.ars.union_rel∗ ⊤ f' := by
    intro n _
    simpa! [f'] using (common_reduct (f' n) (f n)).choose_spec.left

  -- with a corresponding regular reduction sequence
  obtain ⟨N, g, hseq, hgf'₁, hgf'₂⟩ := InfReductionSeq.regular_seq_of_rt_seq f' hf'

  -- and every element in β has a reduct in the sequence
  use N, g, hseq

  constructor
  · intro x
    obtain ⟨n, hn⟩ := hf x
    obtain ⟨m, hm, heq⟩ := hgf'₁ (n + 1)
    use (g m)
    simp [reduction_seq.elems]
    refine ⟨⟨m, hm, rfl⟩, ?_⟩
    · rw [<-heq, <-hn]
      simpa! [f'] using (common_reduct (f' n) (f n)).choose_spec.right
  · simp [reduction_seq.start]
    simp! [f', <-hgf'₂, a']


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

section acyclic_general

variable {r: Rel α α} {N: ℕ∞} {f: ℕ → α} (hseq: reduction_seq r N f)

/--
A reduction sequence is acyclic if two elements
are equal only if their indices are the same.
-/
def reduction_seq.acyclic (hseq: reduction_seq r N f) :=
  ∀⦃n m: ℕ⦄, n < N → m < N → f n = f m → n = m

lemma acyclic_of_succeeds (hcf: cofinal_reduction hseq)
    (a: α) (ha: ∀(n: ℕ), n < N + 1 →  ∃m ≥ n, m < N + 1 ∧ f m = a):
    ∃N' f', ∃(hseq': reduction_seq r N' f'), cofinal_reduction hseq' ∧ hseq'.acyclic := by
  use 0
  use (fun n ↦ a)
  use reduction_seq.refl

  constructor
  · intro x
    use a
    obtain ⟨b', hb'mem, hb'rel⟩ := hcf x
    simp
    simp at hb'mem
    obtain ⟨n, hlt, heq⟩ := hb'mem
    obtain ⟨m, hge, hlt', heq'⟩ := ha n hlt

    have: r∗ b' a := by
      subst heq heq'
      apply reduction_seq.reflTrans hseq _ _ hlt' hge

    trans b'
    exact hb'rel
    exact this
  · simp [reduction_seq.acyclic]

end acyclic_general

section acyclic_finite

/--
The acyclic version of a finite cofinal reduction sequence is simply the
last element of that reduction sequence.
-/

lemma acyclic_of_finite {N: ℕ} {f: ℕ → α} (hseq: reduction_seq r N f) (hcf: cofinal_reduction hseq):
    ∃N' f', ∃(hseq': reduction_seq r N' f'), cofinal_reduction hseq' ∧ hseq'.acyclic := by
  apply acyclic_of_succeeds hseq hcf hseq.end
  intro n hlt
  use N
  simp
  norm_cast at hlt ⊢
  omega

end acyclic_finite

section acyclic_infinite

variable (f: ℕ → α) (n: ℕ) (hseq: reduction_seq r ⊤ f) (hcycle: ¬hseq.acyclic)
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
lemma last_finite_appearance: appears_finitely f n → appears_finitely' f n := by
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

include hcf in
lemma acyclic_of_appears_infinitely (hinf: ∃n, appears_infinitely f n):
    ∃N' f', ∃(hseq': reduction_seq r N' f'), cofinal_reduction hseq' ∧ hseq'.acyclic := by
  apply acyclic_of_succeeds hseq hcf (f (hinf.choose))

  simp
  intro n
  obtain ⟨m, hgt, heq⟩ := hinf.choose_spec n
  use m, (by omega)
  exact heq.symm

section all_appear_finitely

variable (hf: ∀n, appears_finitely' f n)

noncomputable def f_idxs (n: ℕ): ℕ :=
  Classical.choose (hf (if n = 0 then n else (f_idxs (n - 1)) + 1))

noncomputable def f' (n: ℕ) :=
  f <| f_idxs f hf n

include hseq in
lemma hseq': reduction_seq r ⊤ (f' f hf) := by
  intro n _
  dsimp [f']
  nth_rw 2 [f_idxs]

  obtain ⟨heq, -⟩ := (hf ((f_idxs f hf n) + 1)).choose_spec

  simp only [<-heq, ENat.coe_lt_top, hseq]

lemma arg_le_hf (n: ℕ): n ≤ Classical.choose (hf n):= by
  obtain ⟨-, hneq⟩ := (hf n).choose_spec
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
    apply hseq.reflTrans _ _ _ hge
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
  · apply this heq.symm (by tauto) (by omega)

  apply f_idxs_last f hf (f_idxs.strictMono f hf h) heq

include hseq hcf in
/--
Let hseq be an infinite cofinal reduction sequence which contains every element only
finitely often. Then there is an acyclic cofinal reduction sequence, which is constructed
by skipping all cycles in hseq.
-/
lemma acyclic_of_all_appear_finitely (hninf: ¬∃n, appears_infinitely f n):
    ∃f', ∃(hseq': reduction_seq r ⊤ f'), cofinal_reduction hseq' ∧ hseq'.acyclic := by
  have hf: ∀n, appears_finitely' f n := by
    rw [no_appears_infinitely_imp_appears_finitely f] at hninf
    intro n
    exact last_finite_appearance f n (hninf n)

  use f' f hf,
      hseq' r f hseq hf,
      hseq'.cofinal r f hseq hcf hf,
      hseq'.acyclic r f hseq hf

end all_appear_finitely
end acyclic_infinite

section cyclic

variable {r: Rel α α} {N: ℕ∞} {f: ℕ → α}

/-- Any (cyclic) cofinal reduction sequence has an acyclic counterpart. -/
lemma cofinal_reduction_acyclic (hseq: reduction_seq r N f) (hcf: cofinal_reduction hseq):
    ∃(N': _) (f': _) (hseq': reduction_seq r N' f'), cofinal_reduction hseq' ∧ hseq'.acyclic := by
  cases N
  -- If the cofinal reduction sequence is finite, the last element on its own
  -- forms a cofinal reduction sequence which is acyclic.
  case coe N =>
    exact acyclic_of_finite r hseq hcf

  -- If the cofinal reduction sequence is infinite...
  case top =>
    by_cases hinf: ∃n, appears_infinitely f n
    -- ...and at least one element appears infinitely often, that element on
    -- its own forms a cofinal reduction sequence which is acyclic.
    · exact acyclic_of_appears_infinitely r f hseq hcf hinf
    -- ...and all elements appear only finitely often, we are in the complicated
    -- case, where we have to construct a new infinite reduction sequence which
    -- skips all of the cycles.
    · use ⊤
      exact acyclic_of_all_appear_finitely _ _ _ hcf hinf

end cyclic
end
end Thesis
