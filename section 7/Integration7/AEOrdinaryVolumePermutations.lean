import Integration7.OrdinaryVFVolumePermutations
import Integration7.PureVFPermutationDimensions
import Integration7.AEOrdinaryVolumeModules
import Integration7.PositiveVolumeClassScalarExtensions

/-! VF coordinate permutations on ordinary-valued almost-everywhere
functions, including their actual ordinary coefficient action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem ae_ordinary_volume_family_permute_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (σ : Equiv.Perm (Fin (n+1)))
    (h : AEOrdinaryRVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    AEOrdinaryRVVolumeFunctionEquivalent hc C ⟨a,F.permuteBase σ⟩ ⟨b,G.permuteBase σ⟩ := by
  obtain ⟨E,hE,hRows⟩ := h
  refine ⟨(pureVFPermutationMap E σ).image,by rw [pure_vf_permutation_dimension]; exact hE,?_⟩
  intro x hx
  have hy : x ∘ σ.symm ∉ E.carrier := by
    intro h
    apply hx
    refine ⟨⟨x ∘ σ.symm,h⟩,?_⟩
    funext i
    exact congrArg x (σ.symm_apply_apply i)
  rw [permuted_ordinary_volume_family_row_class,permuted_ordinary_volume_family_row_class,hRows _ hy]

def aeOrdinaryRVVolumeFunctionPermuteBase
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) :
    AEOrdinaryRVVolumeFunction hc C n → AEOrdinaryRVVolumeFunction hc C n :=
  Quotient.map (fun F => ⟨F.1,F.2.permuteBase σ⟩)
    (fun F G h => ae_ordinary_volume_family_permute_base hc C F.2 G.2 σ h)

theorem ae_ordinary_volume_permute_base_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) (f g : AEOrdinaryRVVolumeFunction hc C n) :
    aeOrdinaryRVVolumeFunctionPermuteBase hc C σ (f+g) =
      aeOrdinaryRVVolumeFunctionPermuteBase hc C σ f + aeOrdinaryRVVolumeFunctionPermuteBase hc C σ g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G =>
      apply Quotient.sound
      apply ae_ordinary_rv_volume_equivalent_of_pointwise hc C
      intro x
      rw [permuted_ordinary_volume_family_row_class,ordinary_volume_family_coprod_row_class,
        ordinary_volume_family_coprod_row_class,permuted_ordinary_volume_family_row_class,
        permuted_ordinary_volume_family_row_class]
      exact map_add _ _ _

theorem ae_ordinary_volume_permute_base_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) : aeOrdinaryRVVolumeFunctionPermuteBase hc C σ 0 = 0 := by
  apply Quotient.sound
  apply ae_ordinary_rv_volume_equivalent_of_pointwise hc C
  intro x
  rw [permuted_ordinary_volume_family_row_class,ordinary_zero_volume_family_row_class,
    ordinary_zero_volume_family_row_class]
  exact map_zero _

theorem ae_ordinary_volume_permute_base_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) (z : RVVolumeBlowupClasses hc C 0)
    (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeOrdinaryRVVolumeFunctionPermuteBase hc C σ (z • f) =
      z • aeOrdinaryRVVolumeFunctionPermuteBase hc C σ f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_ordinary_rv_volume_equivalent_of_pointwise hc C
      intro x
      rw [permuted_ordinary_volume_family_row_class,ordinary_volume_family_scalar_row_class,
        ordinary_volume_family_scalar_row_class,map_mul,ordinary_volume_coefficient_extend_trans,
        permuted_ordinary_volume_family_row_class]

def aeOrdinaryRVVolumeFunctionPermuteBaseLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) :
    AEOrdinaryRVVolumeFunction hc C n →ₗ[RVVolumeBlowupClasses hc C 0] AEOrdinaryRVVolumeFunction hc C n where
  toFun := aeOrdinaryRVVolumeFunctionPermuteBase hc C σ
  map_add' := ae_ordinary_volume_permute_base_add hc C σ
  map_smul' := ae_ordinary_volume_permute_base_smul hc C σ
end IntegrationInACVF.Section7
