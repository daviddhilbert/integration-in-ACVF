import Integration7.IndexedVolumeAdmissibility
import Integration7.GammaVolumeAlgebraicCenters

/-! The algebraicity of an indexed blowup center is over the original
Gamma base. Finite base-volume fibres retain the index parameters
algebraically; no containing-context parameters enter this claim. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

theorem GammaRVVolumeSchema.indexed_center_algebraic
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (N : ℕ)
    (hvalid : ∀ t ∈ T,
      (⟨F.object,Fin.last k,N⟩ : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv)).valid (rvValues t))
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M)) :
    GammaBlowupCenter (P.inContext hc C hP).toObject B := by
  let A : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv) := ⟨F.object,Fin.last k,N⟩
  have h := A.indexed_admissible BP hvalid P.finite
  intro u
  have hA := h.algebraic ⟨u.val,u.property⟩
  have hi : Fin.natAdd d (Fin.last k) = Fin.last (d+k) := Fin.ext rfl
  rw [hi] at hA
  exact hA

end IntegrationInACVF.Section7
