import Integration7.CanonicalVolumePresentations
import IntegrationSection6.GammaFiniteGraphObjects
import IntegrationSection6.FiniteRVParameterExtension

/-! Finite original-Gamma graph presentations retain their actual finite
map and dimension bound in a containing canonical real base. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a d : ℕ}
variable {D : Set (Fin a → CanonicalRV.RVSort M)}
variable {R : (Fin a → CanonicalRV.RVSort M) → (Fin d → CanonicalRV.RVSort M) → Prop}

def GammaFiniteGraphPresentation.canonicalFinite
    (hc : CanonicalStructure.IsCanonical (M := M))
    (P : GammaFiniteGraphPresentation B a d D R) : RVFiniteObject (M := M) P.codes d :=
  ⟨{ arity := a
     domain := canonicalRawRVDomain hc P.domain
     volume := canonicalRawRVMap hc P.volume },P.finite_volume⟩

def GammaFiniteGraphPresentation.inVolumeContext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaFiniteGraphPresentation B a d D R) (hP : P.codes ⊆ (C.base : Set M)) :
    RVFiniteObject (M := M) (C.base : Set M) d :=
  FiniteRV.extendObject hP (GammaFiniteGraphPresentation.canonicalFinite hc P)

@[simp] theorem GammaFiniteGraphPresentation.inVolumeContext_domain
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaFiniteGraphPresentation B a d D R) (hP : P.codes ⊆ (C.base : Set M)) :
    (GammaFiniteGraphPresentation.inVolumeContext hc C P hP).obj.domain.carrier = D := P.domain_eq

theorem GammaFiniteGraphPresentation.inVolumeContext_dimension
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaFiniteGraphPresentation B a d D R) (hP : P.codes ⊆ (C.base : Set M)) :
    rvDim (GammaFiniteGraphPresentation.inVolumeContext hc C P hP).obj.domain ≤ d := by
  let U := GammaFiniteGraphPresentation.inVolumeContext hc C P hP
  exact (rvDim_le_iff U.obj.domain d).mpr ⟨d,le_rfl,U.obj.volume,U.property⟩

end IntegrationInACVF.Section7
