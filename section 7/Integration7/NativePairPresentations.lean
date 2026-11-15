import Integration7.NativeVFPairImages
import Integration7.GammaNativeCommonNames
import IntegrationSection4.Cells

/-! A Gamma-definable VF pair relation has an actual native VF²
presentation over fixed common names, with its coordinates in the same order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M}

def nativePairLocus (R : Set (VF (M := M) × VF (M := M))) : Set (Point (M := M) 2 0) :=
  {p | twoVFPointPairEquiv p ∈ R}

theorem gamma_native_pair_locus (R : Set (VF (M := M) × VF (M := M)))
    (hR : DefinableOverBase G (fun _ : Fin 2 => .vf) (Cells.pairCodes R)) :
    GammaSetDefinable G (nativePairLocus R) := by
  have he : gammaPointCode '' nativePairLocus R = Cells.pairCodes R := by
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩
      refine ⟨twoVFPointPairEquiv q,hq,?_⟩
      funext i
      fin_cases i <;> rfl
    · rintro ⟨p,hp,rfl⟩
      refine ⟨twoVFPointPairEquiv.symm p,?_,?_⟩
      · exact (twoVFPointPairEquiv.apply_symm_apply p).symm ▸ hp
      · funext i
        fin_cases i <;> rfl
  change DefinableOverBase G (gammaPointSort 2 0) (gammaPointCode '' nativePairLocus R)
  rw [he]
  convert hR using 1
  funext i
  fin_cases i <;> rfl

def nativePairPresentation (R : Set (VF (M := M) × VF (M := M)))
    (hR : DefinableOverBase G (fun _ : Fin 2 => .vf) (Cells.pairCodes R))
    (hNames : commonRealNames G ⊆ S) : DefSet (M := M) S 2 0 :=
  PresentedSet.mk (nativePairLocus R) (SetDefinable.mono _
    (gamma_native_set_common_names (gamma_native_pair_locus R hR)) hNames)

theorem native_pair_presentation_domain (R : Set (VF (M := M) × VF (M := M)))
    (hR : DefinableOverBase G (fun _ : Fin 2 => .vf) (Cells.pairCodes R))
    (hNames : commonRealNames G ⊆ S) : nativeVFPairDomain (nativePairPresentation R hR hNames) = R := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact hq
  · intro hp
    exact ⟨twoVFPointPairEquiv.symm p,(twoVFPointPairEquiv.apply_symm_apply p).symm ▸ hp,
      twoVFPointPairEquiv.apply_symm_apply p⟩

theorem gamma_native_pair_presentation (R : Set (VF (M := M) × VF (M := M)))
    (hR : DefinableOverBase G (fun _ : Fin 2 => .vf) (Cells.pairCodes R))
    (hNames : commonRealNames G ⊆ S) :
    GammaSetDefinable G (carrier (nativePairPresentation R hR hNames)) := gamma_native_pair_locus R hR

end IntegrationInACVF.Section7
