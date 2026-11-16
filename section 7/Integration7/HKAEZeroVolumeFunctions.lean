import Integration7.HKZeroVolumeFamilies
import Integration7.HKVolumeClasses
import Integration7.PureVFDimensionUnions

/-! Weighted measured-zero valued functions modulo equality outside one
same-base VF-small exceptional set. Each good row retains its exact RV
form; no density is forgotten in taking the quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

abbrev ZeroVolumeFunctionPresentation (C : BaseContext M) (n : ℕ) := Σ a, ZeroVFVolumeFamily C n a

def AEZeroVolumeFunctionEquivalent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F G : ZeroVolumeFunctionPresentation C (n+1)) : Prop :=
  ∃ E : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M),
    vfDim (rawRVSpace (M := M) 1) E < n+1 ∧ ∀ x, x ∉ E.carrier →
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.2.rowInContext x) =
        rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.2.rowInContext x)

theorem ae_zero_volume_equivalent_of_pointwise
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {F G : ZeroVolumeFunctionPresentation C (n+1)}
    (h : ∀ x, rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.2.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.2.rowInContext x)) :
    AEZeroVolumeFunctionEquivalent hc C F G :=
  ⟨DefSet.empty _ _,(Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
    (.rv 0)).trans_lt (Nat.zero_lt_succ n),fun x _ => h x⟩

def aeZeroVolumeFunctionSetoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Setoid (ZeroVolumeFunctionPresentation C (n+1)) where
  r := AEZeroVolumeFunctionEquivalent hc C
  iseqv := ⟨fun _ => ae_zero_volume_equivalent_of_pointwise hc C (fun _ => rfl),
    fun ⟨E,hE,h⟩ => ⟨E,hE,fun x hx => (h x hx).symm⟩,
    fun ⟨E,hE,h⟩ ⟨D,hD,g⟩ => ⟨E.union D,by rw [pure_vf_dim_union hc C]; exact max_lt hE hD,
      fun x hx => (h x (fun he => hx (Or.inl he))).trans (g x (fun hd => hx (Or.inr hd)))⟩⟩

abbrev AEZeroVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :=
  Quotient (aeZeroVolumeFunctionSetoid hc C n)

end IntegrationInACVF.Section7.HK
