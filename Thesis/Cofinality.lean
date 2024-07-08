import Thesis.ReductionSeq
import Thesis.ARS
import Thesis.RelProps

namespace Thesis

section

variable {α I}
variable (A: ARS α I)
variable (r: α → α → Prop)

/--
A set `s` is cofinal in r if every element `a: α` reduces to
some b in the set.
-/
def cofinal (s: Set α) := ∀a, ∃b ∈ s, r∗ a b

/--
An infinite reduction sequence (described by f) is cofinal in r if the set
of all elements in the sequence is cofinal in r.
-/
def inf_cofinal_reduction (f: ℕ → α) := inf_reduction_seq r f ∧ cofinal r (f '' Set.univ)

/--
A finite reduction sequence `rs` is cofinal in `A.union_rel` if the set of all elements
in the sequence is cofinal in r.
-/
def ReductionSeq'.cofinal_reduction (r: ReductionSeq' A is as x y) := cofinal A.union_rel {x | x ∈ as}

section cp

variable (a: α)


def fin_cofinality_property (a: α) :=
  ∃is as x y, ∃(r: ReductionSeq' (A.reduction_graph a).ars is as x y), r.cofinal_reduction

def inf_cofinality_property (a: α) :=
  (∃f, inf_cofinal_reduction (A.reduction_graph a).ars.union_rel f)

def cofinality_property := ∀a, fin_cofinality_property A a ∨ inf_cofinality_property A a

example (hsn: strongly_normalizing A.union_rel) (hcp: cofinality_property A): fin_cofinality_property A a := by
  cases hcp a
  · assumption
  · rename_i h
    exfalso
    apply (A.reduction_graph a).down_sn _ hsn
    obtain ⟨f, ⟨hf₁, _⟩⟩ := h
    use f

end cp

end

end Thesis
