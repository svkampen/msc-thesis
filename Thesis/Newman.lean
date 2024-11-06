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

namespace Thesis.Newman

open Relation
open Classical

section newman_barendregt

variable {α} (r: Rel α α)

/-- An ambiguous element `a` has at least two distinct normal forms. -/
def ambiguous (a: α) := ∃(b c: α), normal_form r b ∧ normal_form r c ∧ (b ≠ c) ∧ (r∗ a b ∧ r∗ a c)

/-- Uniqueness of normal forms + weak normalization implies confluence. -/
def unr_wn_imp_confluence {r: Rel α α} (hwn: weakly_normalizing r) (hu: unique_nf_prop_r r): confluent r := by
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
    obtain ⟨d, hd⟩ := hwc (b := b) (c := c) (by tauto)

    obtain ⟨nfd, hnfd⟩ := hwn d

    wlog h: (nfd ≠ d₁) generalizing b c d₁ d₂
    · have h': nfd ≠ d₂ := by cc
      have := this d₂ d₁ hnf₂ hnf₁ (by cc) hpath₂ hpath₁ c hc b hb (by tauto) h'
      assumption

    use b, hb.left, nfd, d₁, hnfd.1, hnf₁, h, Trans.trans (hd.1) (hnfd.2), hb.2


/-- Newman's lemma: strong normalization + local confluence implies confluence. -/
def newman (hsn: strongly_normalizing r) (hwc: weakly_confluent r): confluent r := by
  have hwn: weakly_normalizing r := strongly_normalizing_imp_weakly_normalizing hsn
  suffices hun: unique_nf_prop_r r from @unr_wn_imp_confluence _ _ hwn hun
  contrapose hsn with hun
  simp only [unique_nf_prop_r, not_forall] at hun

  obtain ⟨d₁, d₂, ⟨⟨hnf₁, hnf₂⟩, ⟨a, hpath₁, hpath₂⟩, hne⟩⟩ := hun

  choose! f h₁ h₂ using (newman_ambiguous_step hwn hwc)
  have h₃: ∀N, ambiguous r (f^[N] a) := Function.Iterate.rec _ h₂ (by use d₁, d₂)

  simp [strongly_normalizing]
  use (f^[·] a)
  intro n
  simp only [Function.iterate_succ', Function.comp]
  apply h₁ _ (h₃ n)

end newman_barendregt

-- prerequisites for different proof of Newman's Lemma

/- The transitive closure of `r.inv` is a strict order if `r` is SN. -/
section strict_order_trans_inv

variable {α} {r: Rel α α}

/-- If `r` is strongly normalizing, the transitive closure of `r.inv` is a strict order. -/
instance sn_imp_trans_strict_order [hsn: IsStronglyNormalizing r] : IsStrictOrder α (r.inv)⁺ where
  irrefl := by
    have hwf := (sn_iff_wf_inv r).mpr hsn.1
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
instance sn_imp_wf_trans_inv [hsn: IsStronglyNormalizing r]: IsWellFounded α (r.inv)⁺ where
  wf := by
    obtain ⟨sn⟩ := hsn
    have: WellFounded r.inv := by exact (sn_iff_wf_inv r).mpr sn
    exact WellFounded.transGen this

end strict_order_trans_inv

variable {r: Rel α α}

/-- Newman's Lemma using well-founded induction w.r.t (r.inv)⁺. -/
lemma newman₂ (hsn: strongly_normalizing r) (hwc: weakly_confluent r): confluent r := by
  have: IsStronglyNormalizing r := ⟨hsn⟩
  have hwf: IsWellFounded α (r.inv)⁺ := inferInstance

  rintro a
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

/-- A more specific SymmSeq symmetry lemma for Newman's Lemma. -/
private lemma symm_nm (hseq: SymmSeq r x y ss) (hss: ∀s ∈ ss, s.dir = Direction.FW):
    ∃ss', SymmSeq r y x ss' ∧ ∀s' ∈ ss', ∃s ∈ ss, s' = (s.end, Direction.BW, s.start) := by
  induction hseq with
  | refl => use []; tauto
  | head d hstep hseq ih =>
    rename_i x y z ss
    obtain ⟨ss', hss'⟩ := ih (by intro s hs; apply hss; simp [hs])

    use (ss' ++ [(y, Direction.BW, x)])
    constructor
    · apply SymmSeq.tail
      exact hss'.1
      have: r.dir Direction.FW x y := by
        convert hstep
        rw [<-hss (x, d, y) (List.mem_cons_self _ _)]
      rwa [<-Rel.dir_rev]
    · intro s hs
      simp at hs
      cases' hs with h h
      · have := hss'.2 s h
        simp_all
      · simp_all

/-- In a forward-only SymmSeq, there is a transitive step from the start to the end of any intermediate step. -/
private lemma get_trans_step {step: Step α} (hseq: SymmSeq r x y ss) (hstep': step ∈ ss) (hss: ∀s ∈ ss, s.dir = Direction.FW):
    r⁺ x step.end := by
  induction hseq with
  | refl => contradiction
  | head d hstep hseq ih =>
    rename_i x y z ss
    have hstep_fw: r x y := by
      have: d = Direction.FW :=
        hss (x, d, y) (List.mem_cons_self _ _)
      simp_all [Rel.dir]
    simp at hstep'
    cases' hstep' with h h
    · simp [h, Step.end]
      apply TransGen.single hstep_fw
    have := ih h (by intro s hs; apply hss; simp_all)
    apply TransGen.head hstep_fw this

/-- A single peak-elimination step, used in the peak-elimination proof of Newman's Lemma. -/
private lemma newman_step (hwc: weakly_confluent r) (hseq: SymmSeq r x y ss) (hp: hseq.has_peak):
    ∃(ss': _) (hseq': SymmSeq r x y ss'), MultisetExt (r.inv)⁺ (Multiset.ofList hseq'.elems) (Multiset.ofList hseq.elems)
    := by
  obtain ⟨n, hn, ⟨hbw, hfw⟩⟩ := hp
  have hab := hseq.get_step n (by omega)
  have hac := hseq.get_step (n + 1) (by omega)
  rw [hfw] at hac
  rw [hbw] at hab
  simp [Rel.dir, Rel.inv, flip] at hab
  simp [Rel.dir] at hac
  rw [hseq.step_start_end n hn] at hab

  /-
  We have to treat the case b <- a -> b specially, because in this case the result
  of WCR is empty (b -> b in 0 steps). We simply argue that removing the two steps
  b <- a and a -> b yields a smaller multiset.
  -/
  by_cases h: (ss[n].start = ss[n + 1].end)
  · have hseq₁ := hseq.take n (by omega)
    simp [SymmSeq.elems_eq_elems', SymmSeq.elems'] at hseq₁
    rw [List.getElem_append_left (by simp; omega), List.getElem_map] at hseq₁

    have hseq₂ := hseq.drop (n + 2) (by omega)
    simp [SymmSeq.elems] at hseq₂

    rw [h] at hseq₁

    let ss' := List.take n ss ++ List.drop (n + 2) ss
    have hseq' : SymmSeq r x y ss' := hseq₁.concat hseq₂
    use ss', hseq'

    have: hseq.elems = (hseq.elems.take (n + 1) ++ ([ss[n], ss[n+1]].map (·.end) ++ hseq.elems.drop (n + 3))) := by
      nth_rw 1 [<-List.take_append_drop (n + 1) hseq.elems]
      rw [List.append_cancel_left_eq]
      simp [SymmSeq.elems, Step.end]
      nth_rw 1 [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]
      simp
      constructor <;> (apply List.getElem_map (h := by simp; omega))

    have: Multiset.ofList hseq.elems = Multiset.ofList (hseq.elems.take (n + 1) ++ hseq.elems.drop (n + 3)) + Multiset.ofList ([ss[n], ss[n+1]].map (·.end)) := by
      nth_rw 1 [this]
      simp only [List.cons_append, List.singleton_append, Multiset.coe_add, List.append_assoc, Multiset.coe_eq_coe]
      refine List.Perm.append_left (List.take (n + 1) hseq.elems) ?_
      exact List.perm_append_comm

    have hhseq': Multiset.ofList hseq'.elems = Multiset.ofList (hseq.elems.take (n + 1) ++ hseq.elems.drop (n + 3)) := by
      simp [SymmSeq.elems, ss']

    rw [this, hhseq']
    apply MultisetExt.erase_multiple
    · rfl
    · simp

  /-
  In this case, ss[n].start ≠ ss[n+1].end, so there must be some actual sequence
  of steps `b -> .. -> d <- .. <- c`. We construct this sequence `hseq_mid`, and
  want to show that replacing `b <- a -> c` with `b -> .. -> d <- .. <- c`
  reduces the multiset of sequence elements according to the multiset order extension.
  -/
  obtain ⟨d, hd⟩ := hwc ⟨hab, hac⟩

  have hseq₁ := hseq.take n (by omega)
  have hseq₂ := hseq.drop (n + 2) (by omega)
  simp [SymmSeq.elems] at hseq₁ hseq₂

  have ⟨ss₁, h₁, h₁'⟩ := SymmSeq.if_rt hd.1
  have ⟨ss₃, h₃, h₃'⟩ := SymmSeq.if_rt hd.2
  have ⟨ss₂, h₂, h₂'⟩ := symm_nm h₃ h₃'

  have hseq_mid: SymmSeq r ss[n].start ss[n+1].end (ss₁ ++ ss₂) := by
    apply h₁.concat h₂

  have hss₁₂: (ss₁ ++ ss₂) ≠ [] := by
    intro h
    rw [h] at hseq_mid
    have := hseq_mid.empty_eq
    contradiction

  use (List.take n ss) ++ (ss₁ ++ ss₂) ++ (List.drop (n + 2) ss)

  have hseq': SymmSeq r x y (List.take n ss ++ (ss₁ ++ ss₂) ++ List.drop (n + 2) ss) := by
    simp
    cases' n with n
    · simp_all
      have hne: ss ≠ [] := by refine List.length_pos.mp ?_; exact Nat.lt_of_lt_pred hn
      rw [hseq.first_start hne] at *
      have := hseq_mid.concat hseq₂
      simpa
    · simp_all
      simp [hseq.step_start_end n (by omega)] at hseq₁
      have := (hseq₁.concat hseq_mid).concat hseq₂
      simpa

  use hseq'

  /-
  Now begins the tedious process of massaging `hseq'.elems` and `hseq.elems`
  into a form expected by `MultisetExt1.rel`..
  -/
  let M := hseq.elems.take (n + 1) ++ hseq.elems.drop (n + 2)
  let s := ss[n].end

  obtain ⟨L, b, hLb⟩ := (ss₁ ++ ss₂).eq_nil_or_concat.resolve_left hss₁₂

  have: Multiset.ofList hseq.elems = s ::ₘ Multiset.ofList M := by
    have: s = (hseq.elems[n+1]'(by simp [SymmSeq.elems]; omega)) := by simp [SymmSeq.elems]
    simp [this, M]
    nth_rw 1 [<-List.take_append_drop (n + 1) hseq.elems]
    nth_rw 1 [List.drop_eq_getElem_cons]
    all_goals simp
    omega

  rw [this]

  have: b.end = ss[n+1].end := by
    rw [List.concat_eq_append] at hLb
    rw [hLb] at hseq_mid
    exact hseq_mid.last

  have h: ss[n+1].end = ((((x,Direction.FW,x)::ss).map (Step.end))[n+2]'(by simp; omega)) := by
    simp

  have: List.drop (n + 2) hseq.elems = (b.end) :: List.drop (n + 3) hseq.elems := by
    rw [this, h]
    simp only [SymmSeq.elems]
    simp only [<-List.drop_eq_getElem_cons]

  have h: hseq'.elems = List.take (n + 1) hseq.elems ++ (ss₁ ++ ss₂).map (·.end) ++ List.drop (n + 3) hseq.elems := by
    simp [SymmSeq.elems]

  have: Multiset.ofList (hseq'.elems) = Multiset.ofList (hseq.elems.take (n + 1) ++ hseq.elems.drop (n + 2)) + Multiset.ofList (L.map (·.end)) := by
    nth_rw 1 [this, h, hLb]
    simp [List.perm_append_left_iff]
    rw [List.perm_comm]
    apply List.perm_cons_append_cons
    simp [List.perm_append_comm]


  rw [this]

  /-
  We have now produced `M + L` and `a ::ₘ M` as expected by MultisetExt1.rel.
  We then just have to show that all elements in `L` are smaller than `a`,
  i.e. reducts of `a`.
  -/
  apply TransGen.single
  apply MultisetExt1.rel

  simp
  intro y x d

  intro h
  have: (x, d, y) ∈ L.concat b := by
    rw [List.concat_eq_append]
    rw [List.mem_append]
    left; exact h

  have: (x, d, y) ∈ ss₁ ∨ (x, d, y) ∈ ss₂ := by
    rw [<-hLb] at this
    apply List.mem_append.mp
    exact this


  cases this with
  | inl h =>
    have hab := hseq.get_step n (by omega)
    rw [hbw] at hab
    rw [<-Rel.dir_rev] at hab
    simp [Rel.dir] at hab
    apply TransGen.head hab
    have: y = Step.end (x, d, y) := by simp [Step.end]
    rw [this]
    apply get_trans_step h₁ h h₁'
  | inr h =>
    have hac := hseq.get_step (n + 1) (by omega)
    simp [hfw, Rel.dir] at hac
    obtain ⟨step, hstep⟩ := h₂' (x, d, y) h
    simp at hstep
    have hstep': step = (y, Direction.FW, x) := by
      ext
      · simp [hstep.2]
      · simp [h₃' step hstep.1]
      · simp [hstep.2]
    rw [<-hseq.step_start_end n hn] at hac
    by_cases hy: y = ss[n + 1].end
    · rw [hy]
      apply TransGen.single hac
    · obtain ⟨step₂, hstep₂⟩ := h₃.step_pred ⟨hstep.1, (by simp [hstep', Step.start]; exact hy)⟩
      apply TransGen.head hac
      have: step₂.end = y := by
        rw [hstep₂.2]
        rw [hstep']
      rw [<-this]
      apply get_trans_step h₃ hstep₂.1 h₃'


/-- Newman's Lemma, using a terminating peak-elimination procedure. -/
lemma newman₃ (hsn: strongly_normalizing r) (hwc: weakly_confluent r): confluent r := by
  have: IsStronglyNormalizing r := ⟨hsn⟩
  have hwf: IsWellFounded α (r.inv)⁺ := inferInstance
  have hwf': IsWellFounded (Multiset α) (MultisetExt (r.inv)⁺) := inferInstance

  apply conv_confluent_iff_confluent.mp
  intro a b hab
  have ⟨ss, hab'⟩ := SymmSeq.iff_conv.mp hab

  suffices ∃ss', ∃(hseq': SymmSeq r a b ss'), ¬hseq'.has_peak by
    · obtain ⟨ss', hseq', hnp⟩ := this
      apply hseq'.no_peak_congr hnp

  by_contra! h
  let hset := {M | ∃ss, ∃(hseq: SymmSeq r a b ss), M = Multiset.ofList hseq.elems}
  have hne: hset.Nonempty := ⟨Multiset.ofList hab'.elems, ss, hab', rfl⟩

  obtain ⟨M, hM₁, hM₂⟩ := hwf'.wf.has_min hset hne
  obtain ⟨ss', hseq', hM⟩ := hM₁

  obtain ⟨ss'₂, hseq'₂, hless⟩ := newman_step hwc hseq' (h ss' hseq')
  rw [<-hM] at hless
  apply hM₂ hseq'₂.elems _ hless
  use ss'₂, hseq'₂


end Thesis.Newman
