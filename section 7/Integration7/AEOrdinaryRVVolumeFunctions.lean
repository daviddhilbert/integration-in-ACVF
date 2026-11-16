module

public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.AERVVolumeFunctions
public import Integration7.AllDegreeVolumeClasses

@[expose] public section

/-! The actual almost-everywhere function space with ordinary RV[0]
values. Equality is ordinary RV isomorphism off one original-base
definable VF-small exception; no positive-degree density is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

abbrev OrdinaryVolumeFunctionPresentation (C : BaseContext M) (n : ℕ) := Σ a, OrdinaryVFVolumeFamily C n a

def AEOrdinaryRVVolumeFunctionEquivalent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F G : OrdinaryVolumeFunctionPresentation C (n+1)) : Prop :=
  ∃ E : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M),
    vfDim (rawRVSpace (M := M) 1) E < n+1 ∧ ∀ x, x ∉ E.carrier →
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.2.rowInContext x) =
        rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.2.rowInContext x)

theorem ae_ordinary_rv_volume_equivalent_of_pointwise
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {F G : OrdinaryVolumeFunctionPresentation C (n+1)}
    (h : ∀ x, rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.2.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.2.rowInContext x)) :
    AEOrdinaryRVVolumeFunctionEquivalent hc C F G :=
  ⟨DefSet.empty _ _,(Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
    (.rv 0)).trans_lt (Nat.zero_lt_succ n),fun x _ => h x⟩

def aeOrdinaryRVVolumeFunctionSetoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Setoid (OrdinaryVolumeFunctionPresentation C (n+1)) where
  r := AEOrdinaryRVVolumeFunctionEquivalent hc C
  iseqv := ⟨fun _ => ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun _ => rfl),
    fun ⟨E,hE,h⟩ => ⟨E,hE,fun x hx => (h x hx).symm⟩,
    fun ⟨E,hE,h⟩ ⟨D,hD,g⟩ => ⟨E.union D,by rw [pure_vf_dim_union hc C]; exact max_lt hE hD,
      fun x hx => (h x (fun he => hx (Or.inl he))).trans (g x (fun hd => hx (Or.inr hd)))⟩⟩

abbrev AEOrdinaryRVVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :=
  Quotient (aeOrdinaryRVVolumeFunctionSetoid hc C n)

end IntegrationInACVF.Section7
