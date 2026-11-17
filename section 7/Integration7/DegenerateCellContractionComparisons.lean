module

public import Integration7.FixedLabelSmallVFDimension
public import IntegrationSection4.Cells

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The zero-paradigm graph and singleton-projection cell cases of7.7:
all specified standard contractions have empty essential domains and
compare by an actual original-Gamma volume isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV VF rv carrier GammaSetDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {d : ℕ}

theorem degenerate_cell_contractions_compare {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hPC : P.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 0)
    (hA : GammaSetDefinable P (carrier A))
    (ε : VF (M := M) → VF (M := M)) (t : RV (M := M))
    (hCell : CellData (nativeVFPairDomain A) ε t)
    (hDegenerate : t = rv (0 : VF (M := M)) ∨ ∃ a, first (nativeVFPairDomain A) = {a})
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction (fixedRVLabelDomain A z hz) σ)
    (E : StandardContraction (fixedRVLabelDomain A z hz) τ)
    (hT : GammaProgramDefinable P T.program) (hE : GammaProgramDefinable P E.program) :
    GammaVolumeBlowupEquivalent P (C.base : Set M) 1
      (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT)
      (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 E hE) := by
  have hDim : vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc (fixedRVLabelDomain A z hz)) ≤ 1 := by
    rcases hDegenerate with ht | ⟨a,hFirst⟩
    · have hGraph := graph_of_zero_paradigm hCell ht
      apply fixed_label_vf_dimension_le_one_of_coordinate hc A 0 _ z hz
      apply native_graph_coordinate_determines A ε
      intro p hp
      exact ((Set.ext_iff.mp hGraph p).mp hp).2
    · exact fixed_label_vf_dimension_le_one_of_coordinate hc A 1
        (native_first_singleton_coordinate_determines A a hFirst) z hz
  exact small_dimension_fixed_label_contractions_compare hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT
    (hDim.trans_lt (by decide)) E hE

end IntegrationInACVF.Section7
