import IntegrationSection6.CanonicalContractionPrograms
import IntegrationSection6.ContractionNaturalContractibility
import IntegrationSection6.GammaVFContractiblePullbackMaps
import IntegrationSection6.FiniteGammaPresentationCharts

/-! Canonical identity-head contractions of RV-pullbacks recover their
actual RV objects by full Gamma RV isomorphisms. This does not assume a
global specialness property of arbitrary standard contractions. -/
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

def gammaCanonicalContractionIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {U : DefSet (M := M) S n a} (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program)
    (hVF : ∀ u : U, (C.naturalMap u).val.1 = u.val.1) (hc : Contractible C.toMap) :
    GammaRVIso (gammaPullbackAt hBS U hU hUF).toGamma.toGammaRVObject
      (gammaFiniteContraction hκ hs hreal hBS hU hfin C hC).toGammaRVObject := by
  let V := gammaFiniteContraction hκ hs hreal hBS hU hfin C hC
  let VAt : GammaObjectAt B S n := ⟨ofGamma V,hBS,V.domain_graph,V.volume_graph⟩
  have hV : GammaSetDefinable B (carrier (typedLift C.normalizedObject)) := by
    rw [typedLift_carrier]
    exact V.toGammaRVObject.lift_definable
  let Q := gammaPresentationAt VAt (normalizedTypedLift_presents C.normalizedObject) hV
  let f := typedContractionNaturalMap C
  have hfΓ : GammaGraphDefinable B (pointMapGraph f) := by
    apply GammaGraphDefinable.congr (C.gamma_normalized_natural_graph hBS hU hC)
    intro p q
    rfl
  let e := gammaVFContractiblePullbackIso hBS hU hV hUF Q.object.property f
    (typedContractionNaturalMap_bijective C) (typedContractionNaturalMap_contractible C hVF hc)
    (typedContractionNaturalMap_inverse_contractible C hVF) hfΓ (typedContractionNaturalMap_vf C hVF)
  exact gammaIsoTrans e (gammaPresentationIsoAt VAt (normalizedTypedLift_presents C.normalizedObject) hV).toGamma

theorem exists_canonical_finite_contraction_iso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S n a) (hU : GammaSetDefinable B (carrier U)) (hPull : IsRVPullback (carrier U))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U))) :
    ∃ C : StandardContraction U (Equiv.refl _), ∃ hC : GammaProgramDefinable B C.program,
      Nonempty (GammaRVIso (gammaPullbackAt hBS U hU hUF).toGamma.toGammaRVObject
        (gammaFiniteContraction hκ hs hreal hBS hU hfin C hC).toGammaRVObject) := by
  obtain ⟨C,hC,hVF,hc⟩ := canonical_standard_contraction_exists U hU hPull
  exact ⟨C,hC,⟨gammaCanonicalContractionIso hκ hs hreal hBS hU hfin hUF C hC hVF hc⟩⟩

end IntegrationInACVF.Section6.FiniteRV
