module

public import Integration7.PermutedVolumeFamilies
public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.OrdinaryVolumeCoefficientExtensions
public import Section4.RVIsoTools

@[expose] public section

/-! Literal VF coordinate reindexing of ordinary RV[0]-valued families.
The actual finite RV row is unchanged, in its transported parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}

def OrdinaryVFVolumeFamily.permuteBase (F : OrdinaryVFVolumeFamily C n a)
    (σ : Equiv.Perm (Fin n)) : OrdinaryVFVolumeFamily C n a where
  domain := mixedVFPermutationDomain F.domain σ
  finite_labels x := (F.finite_labels (x ∘ σ.symm)).subset
    (fun _ hr => (mem_mixed_vf_permutation_domain F.domain σ x _).mp hr)

def permutedOrdinaryVolumeFamilyRowIso (F : OrdinaryVFVolumeFamily C n a)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → VFType (M := M)) :
    (F.permuteBase σ).rowInContext x ≅
      Section6.FiniteRV.extendObject (vf_parameter_volume_context_permutation_subset C σ x)
        (F.rowInContext (x ∘ σ.symm)) := by
  let U := (F.permuteBase σ).rowInContext x
  let V := Section6.FiniteRV.extendObject (vf_parameter_volume_context_permutation_subset C σ x)
    (F.rowInContext (x ∘ σ.symm))
  have hUV : U.obj.domain.carrier=V.obj.domain.carrier := by
    ext r
    exact mem_mixed_vf_permutation_domain F.domain σ x r
  exact rvFiniteIsoOfAmbient (rvIsoOfCarrierEq U.obj.domain V.obj.domain U.obj.volume V.obj.volume hUV
    (fun _ => funext (fun i => Fin.elim0 i)))

theorem permuted_ordinary_volume_family_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : OrdinaryVFVolumeFamily C n a)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) ((F.permuteBase σ).rowInContext x) =
      ordinaryVolumeCoefficientExtend hc (vfParameterVolumeContext C (x ∘ σ.symm)) (vfParameterVolumeContext C x)
        (vf_parameter_volume_context_permutation_subset C σ x)
        (rvVolumeBlowupClass hc (vfParameterVolumeContext C (x ∘ σ.symm)) (n := 0) (F.rowInContext (x ∘ σ.symm))) :=
  Quotient.sound ⟨permutedOrdinaryVolumeFamilyRowIso F σ x⟩
end IntegrationInACVF.Section7
