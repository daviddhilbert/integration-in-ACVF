import Integration7.GammaVolumeIndexedPresentations
import Integration7.GammaVolumeAdmissibilityContexts
import IntegrationSection6.GammaSchemaIndexedAdmissibility

/-! Uniform fibre admissibility gives actual last-coordinate
admissibility of the joint indexed volume object. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaRVVolumeSchema.indexed_admissible
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (N : ℕ)
    (hvalid : ∀ t ∈ T,
      (⟨F.object,Fin.last k,N⟩ : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv)).valid (rvValues t))
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M)) :
    BlowupAdmissible (P.inContext hc C hP).toObject := by
  let A : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv) := ⟨F.object,Fin.last k,N⟩
  have h := A.indexed_admissible BP hvalid P.finite
  exact P.blowupAdmissibleInContext hc C hP h

end IntegrationInACVF.Section7
