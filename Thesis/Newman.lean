/-
Newman.lean - three proofs of Newman's Lemma.

We start with Barendregt's proof of Newman's lemma, which makes use of the notion
of an ambiguous element, which always has an ambiguous successor if r is
weakly normalizing and weakly confluent. This contradicts strong normalization.
Therefore, a relation which is strongly normalizing and weakly confluent
cannot have ambiguous elements, hence it must be confluent.

The second proof makes use of well-founded induction.

The third proof uses the notion of an order on conversion sequences, showing that, if `r` is
strongly normalizing and weakly confluent, we can eliminate "peaks" in a conversion sequence
and replace them with valleys in a way that is terminating.
-/
import Thesis.BasicProperties
import Thesis.Multiset

namespace Thesis.Newman

open Relation
open Classical

section newman_barendregt

variable {α} (r: Rel α α)

/-- An ambiguous element `a` has at least two distinct normal forms. -/
def ambiguous (a: α) :=
  ∃(b c: α), r∗ a b ∧ r∗ a c ∧ normal_form r b ∧ normal_form r c ∧ b ≠ c

/-- Uniqueness of normal forms + weak normalization implies confluence. -/
lemma confluent_of_wn_unr ⦃α⦄ ⦃r: Rel α α⦄ (hwn: weakly_normalizing r) (hu: unique_nf_prop_r r): confluent r := by
  rintro a b c ⟨hab, hac⟩

  obtain ⟨d₁, hd₁⟩ := hwn b
  obtain ⟨d₂, hd₂⟩ := hwn c

  have had₁: r∗ a d₁ := ReflTransGen.trans hab hd₁.right
  have had₂: r∗ a d₂ := ReflTransGen.trans hac hd₂.right

  have hdeq: d₁ = d₂ :=
    hu d₁ d₂ a ⟨hd₁.left, hd₂.left⟩ ⟨had₁, had₂⟩

  use d₁, hd₁.right
  rw [hdeq]
  exact hd₂.right

/--
If an element has two distinct normal forms, neither one can be the element itself, so the
reduction sequences a ->> d₁ and a ->> d₂ must be transitive instead of reflexive-transitive.
-/
lemma trans_step_of_two_normal_forms {r: Rel α α} {a d₁ d₂: α}
    (hd₁: normal_form r d₁) (hd₂: normal_form r d₂)
    (had₁: r∗ a d₁) (had₂: r∗ a d₂) (hne: d₁ ≠ d₂): r⁺ a d₁ ∧ r⁺ a d₂ := by
  cases had₁.cases_head <;> cases had₂.cases_head
  all_goals simp_all [TransGen.head'_iff]

/--
In the context of Newman's lemma, an ambiguous element `a` always has a one-step
reduct which is also ambiguous (leading to an infinite sequence).
-/
lemma exists_ambiguous_reduct_of_ambiguous {r: Rel α α} (hwn: weakly_normalizing r) (hwc: weakly_confluent r) (a: α):
  ambiguous r a → ∃b, r a b ∧ ambiguous r b := by
    intro ha
    obtain ⟨d₁, d₂, had₁, had₂, hnf₁, hnf₂, hne⟩ := ha

    -- a ->> d₁ and a ->> d₂ cannot be reflexive
    have ⟨had₁', had₂'⟩: r⁺ a d₁ ∧ r⁺ a d₂ := trans_step_of_two_normal_forms hnf₁ hnf₂ had₁ had₂ hne

    -- Therefore, both must have some initial step a -> b ->> d₁ and a -> c ->> d₂
    -- and a -> b ∧ a -> c => ∃d, b ->> d <<- c.
    obtain ⟨b, hab, hbd₁⟩ := TransGen.head'_iff.mp had₁'
    obtain ⟨c, hac, hcd₂⟩ := TransGen.head'_iff.mp had₂'
    obtain ⟨d, hd⟩ := hwc (b := b) (c := c) (by tauto)

    -- d has some normal form, which cannot be equal to both d₁ _and_ d₂
    obtain ⟨nfd, hnfd⟩ := hwn d

    -- without loss of generality, nfd is distinct from d₁.
    wlog h: nfd ≠ d₁ generalizing b c d₁ d₂
    · have h': nfd ≠ d₂ := by cc
      apply this d₂ d₁ (b := c) (c := b)
      all_goals tauto

    -- but both d₁ and nfd are normal forms of b.
    -- then b must be ambiguous.
    have hb: ambiguous r b := by
      use d₁, nfd
      have hbnfd: r∗ b nfd := hd.1.trans hnfd.2
      and_intros <;> tauto

    use b, hab

lemma not_sn_of_wc_not_un (hwc: weakly_confluent r) (hnu: ¬unique_nf_prop_r r):
    ¬strongly_normalizing r := by
  simp only [unique_nf_prop_r, not_forall] at hnu
  obtain ⟨d₁, d₂, a, ⟨⟨hnf₁, hnf₂⟩, ⟨had₁, had₂⟩, hne⟩⟩ := hnu
  intro hsn
  have hwn: weakly_normalizing r := wn_of_sn hsn
  revert hsn

  choose! f h₁ h₂ using (exists_ambiguous_reduct_of_ambiguous hwn hwc)
  have h₃: ∀N, ambiguous r (f^[N] a) := Function.Iterate.rec _ h₂ (by use d₁, d₂)

  simp [strongly_normalizing]
  use (f^[·] a)
  intro n
  simp only [Function.iterate_succ', Function.comp]
  apply h₁ _ (h₃ n)


/-- Newman's lemma: strong normalization + local confluence implies confluence. -/
lemma newman (hsn: strongly_normalizing r) (hwc: weakly_confluent r): confluent r := by
  have hwn: weakly_normalizing r := wn_of_sn hsn
  suffices hun: unique_nf_prop_r r from confluent_of_wn_unr hwn hun
  contrapose hsn with hun
  exact not_sn_of_wc_not_un r hwc hun

end newman_barendregt

-- prerequisites for different proof of Newman's Lemma

/- The transitive closure of `r.inv` is a strict order if `r` is SN. -/
section strict_order_trans_inv

variable {α} {r: Rel α α}

/-- If `r` is strongly normalizing, the transitive closure of `r.inv` is a strict order. -/
instance inv_trans_strict_order_of_sn (hsn: strongly_normalizing r) : IsStrictOrder α (r.inv)⁺ where
  irrefl := by
    have hwf := (sn_iff_wf_inv r).mpr hsn
    have hwf' := WellFounded.transGen hwf
    have hsn' := (sn_iff_wf_inv r⁺).mp ?_
    · contrapose! hsn'
      obtain ⟨a, ha⟩ := hsn'
      intro h
      apply h (fun _ ↦ a)
      simpa using ha
    · convert hwf' using 1
      ext
      simp [Rel.inv, Function.flip_def]
      nth_rw 1 [<-Function.swap_def]
      simp only [transGen_swap]

/-- If `r` is strongly normalizing, the transitive closure of `r.inv` is well-founded. -/
instance wf_inv_trans_of_sn (hsn: strongly_normalizing r): IsWellFounded α (r.inv)⁺ where
  wf := by
    have: WellFounded r.inv := by exact (sn_iff_wf_inv r).mpr hsn
    exact WellFounded.transGen this

end strict_order_trans_inv

variable {r: Rel α α}

/-- Newman's Lemma using well-founded induction w.r.t (r.inv)⁺. -/
lemma newman₂ (hsn: strongly_normalizing r) (hwc: weakly_confluent r): confluent r := by
  have hwf: IsWellFounded α (r.inv)⁺ := wf_inv_trans_of_sn hsn

  intro a
  induction' a using hwf.induction with a wf_ih
  rintro b c ⟨hab, hac⟩

  /-
  r∗ a b is either a = b, or r a b' and r∗ b' b.
  If a = b, then b and c converge at c.

  Similarly for r∗ a c. The non-trivial case is `c *<- c' <- a -> b' ->* b`.
  -/
  rcases hab.cases_head with rfl | ⟨b', hab', hb'b⟩
  · use c
  rcases hac.cases_head with rfl | ⟨c', hac', hc'c⟩
  · use b

  clear hab hac

  /- By well-founded induction, b' and c' are confluent as they are reducts of a. -/
  have hconb': confluent' r b' := wf_ih b' (TransGen.single hab')
  have hconc': confluent' r c' := wf_ih c' (TransGen.single hac')

  /- b' and c' converge at some point d' by weak confluence. -/
  obtain ⟨d', hb'd', hc'd'⟩ := hwc ⟨hab', hac'⟩

  /- b' ->* b and b' ->* d', so by confluence b and d' converge at some point e. -/
  obtain ⟨e, hbe, hd'e⟩ := hconb' ⟨hb'b, hb'd'⟩

  /- c' ->* c and c' ->* d' ->* e, so c and e converge at some point d. -/
  obtain ⟨d, hcd, hed⟩ := hconc' ⟨hc'c, ReflTransGen.trans hc'd' hd'e⟩

  /- This point d is the point where b and c converge. -/
  use d, ReflTransGen.trans hbe hed, hcd


-- Prerequisites for 3rd proof of Newman's Lemma.

/--
If a landscape contains a peak, there must be a landscape whose elements
are smaller than our original landscape according to the multiset order.
-/
private lemma newman_step' (hwc: weakly_confluent r) (hseq: ReductionSeq (SymmGen r) x y ss) (hp: hseq.has_peak):
    ∃(ss': _) (hseq': ReductionSeq (SymmGen r) x y ss'),
      MultisetExt (r.inv)⁺ (Multiset.ofList hseq'.elems) (Multiset.ofList hseq.elems)
    := by
  obtain ⟨n, hn, hab, hac⟩ := hp
  rw [hseq.step_start_stop n hn] at hab

  have hseq₁ := hseq.take n (by omega)
  have hseq₂ := hseq.drop (n + 2) (by omega)

  /-
  We have to treat the case b <- a -> b specially, because in this case the result
  of WCR is empty (b -> b in 0 steps). We simply argue that removing the two steps
  b <- a and a -> b yields a smaller multiset.
  -/
  by_cases h: (ss[n].start = ss[n + 1].stop)
  · have: (ss.map RSStep.start ++ [y])[n]'(by simp; omega) = (ss.map RSStep.start)[n]'(by simp; omega) :=
      List.getElem_append_left (by simp; omega)

    simp_rw [hseq.elems_eq_elems', ReductionSeq.elems', this, List.getElem_map, h] at hseq₁
    simp [ReductionSeq.elems] at hseq₂

    let ss' := ss.take n ++ ss.drop (n + 2)
    use ss', hseq₁.concat hseq₂

    have heq_ss: ss = ss.take n ++ (ss.drop n).take 2 ++ ss.drop (n + 2) := by
      simp [List.take_append_drop]

    apply MultisetExt.erase_multiple (Multiset.ofList $ ((ss.drop n).take 2).map RSStep.stop)
    simp [ReductionSeq.elems]
    nth_rw 2 [heq_ss]
    simp only [ss', List.map_append, List.map_take, List.map_drop, List.append_assoc]
    simp_rw [List.perm_append_left_iff, List.perm_append_comm]

    simp
    omega

  /-
  In this case, ss[n].start ≠ ss[n+1].end, so there must be some actual sequence
  of steps `b -> .. -> d <- .. <- c`. We construct this sequence `hseq_mid`, and
  want to show that replacing `b <- a -> c` with `b -> .. -> d <- .. <- c`
  reduces the multiset of sequence elements according to the multiset order extension.
  -/
  obtain ⟨d, hbd, hcd⟩ := hwc ⟨hab, hac⟩

  obtain ⟨ss₁, hbd⟩ := ReductionSeq.exists_iff_rel_star.mp hbd
  obtain ⟨ss₂', hcd⟩ := ReductionSeq.exists_iff_rel_star.mp hcd

  obtain hbd' := hbd.to_symmgen
  obtain hcd' := hcd.to_symmgen.symmgen_reverse

  let ss₂ := (ReductionSeq.steps_reversed ss₂')

  have hseq_mid := hbd'.concat hcd'

  simp [ReductionSeq.elems_eq_elems', ReductionSeq.elems'] at hseq₁
  have: n < ((List.map RSStep.start ss)).length := by
    simp; omega
  simp [List.getElem_append_left this] at hseq₁
  simp [ReductionSeq.elems] at hseq₂

  have hseq' := (hseq₁.concat hseq_mid).concat hseq₂

  apply Exists.intro
  use hseq'

  /-
  Now begins the tedious process of massaging `hseq'.elems` and `hseq.elems`
  into a form expected by `MultisetExt1.rel`..
  -/
  let M := hseq.elems.take (n + 1) ++ hseq.elems.drop (n + 2)
  let s := ss[n].stop

  have hss₁₂: (ss₁ ++ ss₂) ≠ [] := by
    intro h
    simp [ss₂] at h
    rcases h with ⟨rfl, h⟩
    simp! [h] at hseq_mid
    contradiction

  obtain ⟨L, b, hLb⟩ := (ss₁ ++ ss₂).eq_nil_or_concat.resolve_left hss₁₂

  have: Multiset.ofList hseq.elems = s ::ₘ Multiset.ofList M := by
    have: s = (hseq.elems[n+1]'(by simp [ReductionSeq.elems]; omega)) := by simp [ReductionSeq.elems]
    simp [this, M]
    nth_rw 1 [<-List.take_append_drop (n + 1) hseq.elems]
    nth_rw 1 [List.drop_eq_getElem_cons]
    · simp
    · simp [ReductionSeq.elems]
      omega

  rw [this]

  have: b.stop = ss[n+1].stop := by
    rw [List.concat_eq_append] at hLb
    rw [hLb] at hseq_mid
    exact hseq_mid.last

  have h: ss[n+1].stop = (((⟨x,x⟩::ss).map (RSStep.stop))[n+2]'(by simp; omega)) := by
    simp

  have: List.drop (n + 2) hseq.elems = (b.stop) :: List.drop (n + 3) hseq.elems := by
    rw [this, h]
    simp [ReductionSeq.elems]
    have: n + 1 < (List.map RSStep.stop ss).length := by
      simp
      omega
    rw [List.drop_eq_getElem_cons]
    · simp [List.getElem_map (h := this)]
    · exact this

  have h: hseq'.elems = List.take (n + 1) hseq.elems ++ (ss₁ ++ ss₂).map (·.stop) ++ List.drop (n + 3) hseq.elems := by
    simp [ReductionSeq.elems]

  have: Multiset.ofList (hseq'.elems) = Multiset.ofList (hseq.elems.take (n + 1) ++ hseq.elems.drop (n + 2)) + Multiset.ofList (L.map (·.stop)) := by
    nth_rw 1 [this, h, hLb]
    simp [List.perm_append_left_iff]
    rw [List.perm_comm]
    apply List.perm_cons_append_cons
    simp [List.perm_append_comm]

  rw [this]

  apply TransGen.single
  constructor

  /- All that's left now is proving that every element in L is a reduct of s. -/
  simp [s]

  intro s hs

  simp_rw [<-hseq.step_start_stop n (by omega)] at hab hac
  simp_rw [TransGen.head'_iff]

  obtain (hmem | hmem): s ∈ ss₁ ∨ s ∈ ss₂ := by
    simp [List.mem_append.mp, hLb, hs]

  · use ss[n].start, hab
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨k, hk, rfl⟩ := hmem
    have := hbd.take (k + 1) (by omega)
    simpa [ReductionSeq.elems] using this.to_reflTrans
  · use ss[n + 1].stop, hac
    have := ReductionSeq.steps_reversed_mem hmem
    simp [ss₂, List.mem_iff_getElem] at this
    obtain ⟨k, hk, heq⟩ := this
    have: s.stop = ss₂'[k].start := by rw [heq]
    rw [this]
    have := hcd.take k (by omega)
    simp_rw [ReductionSeq.elems_eq_elems', ReductionSeq.elems'] at this
    have hlt: k < (ss₂'.map RSStep.start).length := by simp [hk]
    simp_rw [List.getElem_append_left hlt] at this
    simpa using this.to_reflTrans


/-- Newman's Lemma, using a terminating peak-elimination procedure. -/
lemma newman₃ (hsn: strongly_normalizing r) (hwc: weakly_confluent r): confluent r := by
  have hwf: IsWellFounded α (r.inv)⁺ := wf_inv_trans_of_sn hsn
  have hwf': IsWellFounded (Multiset α) (MultisetExt (r.inv)⁺) := inferInstance

  /- It suffices that r is conversion confluent. -/
  suffices h: conv_confluent r
  · rwa [conv_confluent_iff_confluent] at h

  intro a b hab

  /- If a ≡ b, there must exist a landscape between a and b. -/
  have ⟨ss, hab'⟩ := ReductionSeq.exists_iff_rel_conv.mp hab

  /-
  It suffices to show that there exists a landscape between a and b
  that does not contain any peaks.
  -/
  suffices ∃ss', ∃(hseq': ReductionSeq (SymmGen r) a b ss'), ¬hseq'.has_peak by
    · obtain ⟨ss', hseq', hnp⟩ := this
      apply hseq'.reduct_of_not_peak hnp

  /-
  The multiset order has a minimum on every set, so also on the set of multisets
  of landscapes between a and b.
  -/
  let hset := {M | ∃ss, ∃(hseq: ReductionSeq (SymmGen r) a b ss), M = Multiset.ofList hseq.elems}
  have hne: hset.Nonempty := ⟨Multiset.ofList hab'.elems, ss, hab', rfl⟩

  obtain ⟨M, hM₁, hM₂⟩ := hwf'.wf.has_min hset hne
  obtain ⟨ss', hseq', hM⟩ := hM₁

  /- Let's say all landscapes between a and b contain a peak. -/
  by_contra! h

  /-
  Then our minimum is not a minimum, because any landscape with a peak
  can use newman_step' to produce a smaller landscape.
  -/
  obtain ⟨ss'₂, hseq'₂, hless⟩ := newman_step' hwc hseq' (h ss' hseq')
  rw [<-hM] at hless
  apply hM₂ hseq'₂.elems _ hless
  use ss'₂, hseq'₂


end Thesis.Newman
