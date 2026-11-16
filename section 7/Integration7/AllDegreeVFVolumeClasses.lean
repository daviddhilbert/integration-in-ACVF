module

public import Integration7.ZeroVolumeIntegration
public import Integration7.PositiveVFVolumeAdditiveStructure

@[expose] public section

/-! Actual VF volume isomorphism classes in all degrees, including the
ordinary degree-zero category. Additive structures are supplied explicitly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def VFVolumeIsoInDegree (S : Set M) : (n : ℕ) → VFVolumeObject (M := M) S n → VFVolumeObject (M := M) S n → Type
  | 0, A, B => A ≅ B
  | _+1, A, B => VFVolumeIso A B

abbrev VFVolumeIsoClasses
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) : ℕ → Type
  | 0 => ZeroVFVolumeIsoClasses C
  | k+1 => PositiveVFVolumeIsoClasses hc C k

def vfVolumeIsoClass (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    {n : ℕ} → VFVolumeObject (M := M) (C.base : Set M) n → VFVolumeIsoClasses hc C n
  | 0, A => zeroVFVolumeIsoClass C A
  | _+1, A => positiveVFVolumeIsoClass hc C A

abbrev vfVolumeIsoClassesAdd
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    (n : ℕ) → Add (VFVolumeIsoClasses hc C n)
  | 0 => zeroVFVolumeIsoClassesAdd hc C
  | k+1 => positiveVFVolumeIsoClassesAdd hc C k

abbrev vfVolumeIsoClassesZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    (n : ℕ) → Zero (VFVolumeIsoClasses hc C n)
  | 0 => zeroVFVolumeIsoClassesZero hc C
  | k+1 => positiveVFVolumeIsoClassesZero hc C k

def vfVolumeIsoClassesAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    (n : ℕ) → AddCommMonoid (VFVolumeIsoClasses hc C n)
  | 0 => zeroVFVolumeAddCommMonoid hc C
  | k+1 => positiveVFVolumeAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := k)

end IntegrationInACVF.Section7
