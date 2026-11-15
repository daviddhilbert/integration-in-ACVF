import Integration7.PointwiseRVVolumeFunctions
import Integration7.VFBaseDimensionBounds
import Integration7.PureVFDimensionUnions
import Section4.VFUnions

/-! Positive homogeneous definable RV-volume functions modulo equality
outside a definable VF-small base set. Pointwise equality maps onto this
quotient; an integral on this larger quotient requires its own descent proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}

def AERVVolumeFunctionEquivalent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F G : SelectedVolumeFunctionPresentation C (n+1) k) : Prop :=
  ∃ E : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M),
    vfDim (rawRVSpace (M := M) 1) E < n+1 ∧
      ∀ x, x ∉ E.carrier →
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.2.rowInContext x) =
          positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (G.2.rowInContext x)

theorem ae_rv_volume_function_equivalent_of_pointwise
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {F G : SelectedVolumeFunctionPresentation C (n+1) k}
    (h : ∀ x, positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.2.rowInContext x) =
      positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (G.2.rowInContext x)) :
    AERVVolumeFunctionEquivalent hc C F G :=
  ⟨DefSet.empty _ _,(Dimension.dim_empty rawVFSpace
    (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) (.rv 0)).trans_lt (Nat.zero_lt_succ n),fun x _ => h x⟩

def aeRVVolumeFunctionSetoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    Setoid (SelectedVolumeFunctionPresentation C (n+1) k) where
  r := AERVVolumeFunctionEquivalent hc C
  iseqv := ⟨fun _ => ae_rv_volume_function_equivalent_of_pointwise hc C (fun _ => rfl),
    fun ⟨E,hE,h⟩ => ⟨E,hE,fun x hx => (h x hx).symm⟩,
    fun ⟨E,hE,h⟩ ⟨D,hD,g⟩ => ⟨E.union D,by
      rw [pure_vf_dim_union hc C]
      exact max_lt hE hD,
      fun x hx => (h x (fun he => hx (Or.inl he))).trans (g x (fun hd => hx (Or.inr hd)))⟩⟩

abbrev AERVVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :=
  Quotient (aeRVVolumeFunctionSetoid hc C n k)

def pointwiseToAERVVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    PointwiseRVVolumeFunction hc C (n+1) k → AERVVolumeFunction hc C n k :=
  Quotient.lift (Quotient.mk (aeRVVolumeFunctionSetoid hc C n k))
    (fun _ _ h => Quotient.sound (ae_rv_volume_function_equivalent_of_pointwise hc C h))

theorem pointwise_to_ae_rv_volume_function_surjective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Function.Surjective (pointwiseToAERVVolumeFunction hc C (n := n) (k := k)) := by
  intro f
  induction f using Quotient.inductionOn with
  | h F => exact ⟨Quotient.mk _ F,rfl⟩

end IntegrationInACVF.Section7
