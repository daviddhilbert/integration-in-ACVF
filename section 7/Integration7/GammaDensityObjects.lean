import Integration7.GammaVolumeGraphPresentations
import IntegrationSection6.GammaNativeFiniteBounds

/-! A volume density itself is an original-Gamma RV-valued function.
It need not have finite fibres. Its native raw graph retains exact
functionality and nonvanishing, which are the inputs to promotion. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
variable {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

def GammaVolumeGraphPresentation.densityObject (P : GammaVolumeGraphPresentation B a k D R W) :
    GammaRVObject B 1 where
  codes := P.finite.codes
  real_contains := P.finite.real_contains
  object := @RVObject.mk M (@CanonicalStructure.normalize M sM) P.finite.codes 1 a P.finite.domain
    (@VolumeForm.map M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) _ P.finite.codes P.finite.domain P.form)
  domain_graph := P.finite.toGamma.domain_graph
  volume_graph := GammaGraphDefinable.congr P.density_graph (fun p q => (P.density_iff p.2 q.2).symm)

theorem GammaVolumeGraphPresentation.rawDensity_nonzero
    (P : GammaVolumeGraphPresentation B a k D R W) (x : Fin a → M) (y : Fin 1 → M)
    (h : Fin.append x y ∈ gammaRawObjectVolume P.densityObject) : y 0 ≠ iRVZero := by
  obtain ⟨u,_,hy⟩ := (gammaRawObjectVolume_append_iff P.densityObject x y).mp h
  have hn := (@rv_nonzero_iff_raw M (@CanonicalStructure.normalize M sM)
    (@CanonicalStructure.normalized_model M sM hM)
    (@VolumeForm.value M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) _ P.finite.codes P.finite.domain P.form u)).mp
    (@VolumeForm.nonzero M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) _ P.finite.codes P.finite.domain P.form u)
  exact (congrFun hy 0) ▸ hn

end IntegrationInACVF.Section7
