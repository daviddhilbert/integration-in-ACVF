module

public import Integration7.SelectedVolumeBaseRestrictions
public import Integration7.SupportedVolumeFunctionAddition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Restricting actual representatives to a definable VF set descends
to AE functions and retracts the supported presentation quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem ae_volume_base_restriction_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (h : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    AERVVolumeFunctionEquivalent hc C ⟨a,F.onBase X⟩ ⟨b,G.onBase X⟩ := by
  obtain ⟨E,hE,hRows⟩ := h
  refine ⟨E,hE,?_⟩
  intro x hx
  by_cases hX : x ∈ X.carrier
  · rw [selected_volume_on_base_row_class_inside hc F X x hX,
      selected_volume_on_base_row_class_inside hc G X x hX]
    exact hRows x hx
  · rw [selected_volume_on_base_row_class_outside hc F X x hX,
      selected_volume_on_base_row_class_outside hc G X x hX]

def aeVolumeFunctionRestrictToSupported
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    AERVVolumeFunction hc C n k → SupportedAERVVolumeFunction hc C X k :=
  Quotient.map (fun F => ⟨F.1,⟨F.2.onBase X,selected_volume_family_on_base_supported F.2 X⟩⟩)
    (fun F G h => ae_volume_base_restriction_congr hc C X F.2 G.2 h)

theorem selected_supported_volume_row_class_outside
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (X : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier)
    (x : Fin n → VFType (M := M)) (hx : x ∉ X.carrier) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x) = 0 := by
  apply positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x)
  apply RVVolumeIso.of_empty hc (vfParameterVolumeContext C x) _ _ _ rfl
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  exact hx (hF ⟨(x,r),hr⟩)

theorem ae_volume_restriction_forget_supported
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (f : SupportedAERVVolumeFunction hc C X k) :
    aeVolumeFunctionRestrictToSupported hc C X (supportedVolumeFunctionForget hc C X f) = f := by
  induction f using Quotient.inductionOn with
  | h F =>
    apply Quotient.sound
    apply ae_rv_volume_function_equivalent_of_pointwise hc C
    intro x
    by_cases hx : x ∈ X.carrier
    · exact selected_volume_on_base_row_class_inside hc F.2.val X x hx
    · exact (selected_volume_on_base_row_class_outside hc F.2.val X x hx).trans
        (selected_supported_volume_row_class_outside hc X F.2.val F.2.property x hx).symm
end IntegrationInACVF.Section7
