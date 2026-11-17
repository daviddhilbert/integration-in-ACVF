module

public import Integration7.SelectedJacobianRowComparison
public import Integration7.AERVVolumeFunctions
public import Integration7.DefinableMapPreimages
public import Integration7.PureVFPermutationDimensions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Jacobian transform preserves equality almost everywhere.
The exceptional target set is the definable image of the source
exceptional set, and has the same VF dimension as its restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_jacobian_row_empty_outside
    (C : BaseContext M) {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (y : Fin n → VFType (M := M)) (hy : y ∉ Y.carrier) :
    ((F.jacobianPushforward φ hφ hF).rowInContext y).underlying.obj.domain.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro r ⟨p,hp⟩
  have he : (φ ⟨p.val.1,hF p⟩).val = y := congrArg Prod.fst hp
  exact hy (he ▸ (φ ⟨p.val.1,hF p⟩).property)

theorem selected_jacobian_preserves_ae_equivalence
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hG : ∀ p : G.domain, p.val.1 ∈ X.carrier)
    (h : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    AERVVolumeFunctionEquivalent hc C ⟨a,F.jacobianPushforward φ hφ hF⟩
      ⟨b,G.jacobianPushforward φ hφ hG⟩ := by
  obtain ⟨E,hE,hRows⟩ := h
  let D := definableMapPreimage (Map.id X) E
  have hDX : D.carrier ⊆ X.carrier := definableMapPreimage_subset _ _
  have hDE : D.carrier ⊆ E.carrier := by rintro z ⟨x,rfl,hx⟩; exact hx
  let f := φ.restrict (A' := D) hDX
  have hf : Function.Bijective f.toImage := by
    constructor
    · intro u v huv
      apply Subtype.ext
      have hval : (φ ⟨u.val,hDX u.property⟩).val = (φ ⟨v.val,hDX v.property⟩).val :=
        congrArg (fun w : f.image => w.val) huv
      exact congrArg (fun z : X => z.val) (hφ.1 (Subtype.ext hval))
    · rintro ⟨v,u,hu⟩
      exact ⟨u,Subtype.ext hu⟩
  refine ⟨f.image,?_,?_⟩
  · rw [pure_vf_dimension_eq_of_bijective f.toImage hf]
    exact (Dimension.dim_mono rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
      hDE ⟨n+1,pure_vf_has_dimension_bound E⟩).trans_lt hE
  · intro y hy
    by_cases hyY : y ∈ Y.carrier
    · let z : Y := ⟨y,hyY⟩
      have hxE : (φ.inverse hφ z).val ∉ E.carrier := by
        intro hx
        have hxD : (φ.inverse hφ z).val ∈ D.carrier := ⟨φ.inverse hφ z,rfl,hx⟩
        exact hy ⟨⟨(φ.inverse hφ z).val,hxD⟩,congrArg Subtype.val (Map.apply_inverse φ hφ z)⟩
      exact (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C y)).mpr
        (selected_jacobian_row_comparison hc C F G φ hφ hF hG z
          ((positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C (φ.inverse hφ z).val)).mp
            (hRows _ hxE)))
    · exact positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C y)
        (RVVolumeIso.of_empty hc (vfParameterVolumeContext C y) _ _
          (selected_jacobian_row_empty_outside C F φ hφ hF y hyY)
          (selected_jacobian_row_empty_outside C G φ hφ hG y hyY))

end IntegrationInACVF.Section7
