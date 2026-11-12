import IntegrationSection6.GammaContractionPresentationIsomorphisms
import IntegrationSection6.ContractionExtensionIndices
import IntegrationSection6.EmptySelectedContractions

/-! A recursive finite presentation with no selected old RV labels gives
the ordinary RV[n] contraction object, retaining the actual Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}
variable {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

def gammaOrdinaryContractionPresentationIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program)
    (P : GammaSelectedRVPresentation B C.target (orderedSelectedIndex C.program (Fin.elim0 : Fin 0 → Fin a))) :
    GammaRVIso P.toGamma.toGammaRVObject
      (gammaCastDegree (orderedVolumeDegree_eq n 0).symm
        (gammaFiniteContraction hκ hs hreal hBS hU hfinU C hC)).toGammaRVObject :=
  gammaIsoTrans (gammaContractionPresentationIso hκ hs hreal hBS hU Fin.elim0
    (empty_selected_fibres U hfinU) C hC P)
    (gammaRVIsoCastDegree (orderedVolumeDegree_eq n 0).symm
      (gammaEmptySelectedContractionIso hκ hs hreal hBS hU hfinU C hC))

end IntegrationInACVF.Section6.FiniteRV
