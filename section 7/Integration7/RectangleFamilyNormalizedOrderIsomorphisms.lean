module

public import Integration7.RectangleFamilyGammaOrderIsomorphisms
public import Integration7.GammaIsoCoordinateIdentities
public import Integration7.ContractionRetainedDensityLabels

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Normalizing the two actual rectangle contraction objects retains
the full original-Gamma comparison and every original density label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (hGC : G.real ⊆ (C.base : Set M))
variable {H : DefSet (M := M) (C.base : Set M) 2 m}
variable (hH : GammaSetDefinable G (carrier H))
variable (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier H}.Finite)
variable {hRect : RectangularRVFibres (carrier H)} (F : IndependentRectangleFamilyPreparations G H hRect)

def normalizedGammaOrderIso :
    GammaRVIso
      (FiniteRV.gammaFiniteContraction hκ hs hreal hGC hH hfin F.headContraction (F.head_contraction_gamma hH)).toGammaRVObject
      (FiniteRV.gammaFiniteContraction hκ hs hreal hGC hH hfin F.tailContraction (F.tail_contraction_gamma hH)).toGammaRVObject :=
  FiniteRV.gammaIsoTrans
    (FiniteRV.gammaIsoSymm (FiniteRV.gammaRawFiniteNormalizationIso hκ hs hreal hGC hH hfin
      F.headContraction (F.head_contraction_gamma hH)))
    (FiniteRV.gammaIsoTrans (F.rawGammaOrderIso hκ hs hreal hc C hGC hH hfin)
      (FiniteRV.gammaRawFiniteNormalizationIso hκ hs hreal hGC hH hfin
        F.tailContraction (F.tail_contraction_gamma hH)))

theorem normalized_gamma_order_coordinates :
    ∀ u, gammaVolumeValue
      (FiniteRV.gammaFiniteContraction hκ hs hreal hGC hH hfin F.tailContraction (F.tail_contraction_gamma hH)).toGammaRVObject
      ((F.normalizedGammaOrderIso hκ hs hreal hc C hGC hH hfin).equiv u) =
        gammaVolumeValue
          (FiniteRV.gammaFiniteContraction hκ hs hreal hGC hH hfin F.headContraction (F.head_contraction_gamma hH)).toGammaRVObject u := by
  exact gamma_iso_trans_coordinates _ _
    (gamma_iso_symm_coordinates _ (fun u => toFirstVolume_volume _ _ u))
    (gamma_iso_trans_coordinates _ _ (F.raw_gamma_order_coordinates hκ hs hreal hc C hGC hH hfin)
      (fun u => toFirstVolume_volume _ _ u))

theorem normalized_gamma_order_retained_labels (i : Fin m) :
    ∀ u, ((F.normalizedGammaOrderIso hκ hs hreal hc C hGC hH hfin).equiv u).val
      (FiniteRV.contractionOldLabelIndex F.tailContraction i) =
        u.val (FiniteRV.contractionOldLabelIndex F.headContraction i) := by
  exact gamma_iso_trans_labels _ _ _ _ _
    (gamma_iso_symm_labels _ _ _ (fun u => toFirstVolume_oldLabels _ _ _ _))
    (gamma_iso_trans_labels _ _ _ _ _
      (F.raw_gamma_order_retained_labels hκ hs hreal hc C hGC hH hfin i)
      (fun u => toFirstVolume_oldLabels _ _ _ _))

end IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
