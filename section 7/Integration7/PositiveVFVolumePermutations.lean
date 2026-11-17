module

public import Integration7.MixedVFPermutationDomains
public import Integration7.VolumeDensityGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! VF coordinate permutations of positive volume objects transport
their actual domains and densities. No claim that the coordinate map
itself preserves volume is made. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveVFVolumeObject.permuteVF (U : PositiveVFVolumeObject (M := M) S k)
    (σ : Equiv.Perm (Fin (k+1))) : PositiveVFVolumeObject (M := M) S k where
  arity := U.arity
  domain := mixedVFPermutationDomain U.domain σ
  finite_labels x := (U.finite_labels (x ∘ σ.symm)).subset
    (fun r hr => (mem_mixed_vf_permutation_domain U.domain σ x r).mp hr)
  form := U.form.pullback
    ((mixedVFPermutationBijection U.domain σ).inverse (mixed_vf_permutation_bijective U.domain σ))

theorem PositiveVFVolumeObject.permuteVF_density (U : PositiveVFVolumeObject (M := M) S k)
    (σ : Equiv.Perm (Fin (k+1))) (q : (U.permuteVF σ).domain) :
    (U.permuteVF σ).form.value q = U.form.value
      ⟨(q.val.1 ∘ σ.symm,q.val.2),(mem_mixed_vf_permutation_domain U.domain σ q.val.1 q.val.2).mp q.property⟩ := by
  apply congrArg U.form.value
  exact Subtype.ext (mixed_vf_permutation_inverse_value U.domain σ q)

def permutedVFDensityGraphBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    VFVolumeBijection (U.permuteVF σ) (U.densityGraph.permuteVF σ) := by
  let i := (mixedVFPermutationBijection U.domain σ).inverse (mixed_vf_permutation_bijective U.domain σ)
  let g := (appendDensityMap U.form).toImage
  let j := mixedVFPermutationBijection U.densityGraph.domain σ
  let f := j.comp (g.comp i)
  have hi : Function.Bijective i :=
    (Equiv.ofBijective (mixedVFPermutationBijection U.domain σ) (mixed_vf_permutation_bijective U.domain σ)).symm.bijective
  have hf : Function.Bijective f := (mixed_vf_permutation_bijective U.densityGraph.domain σ).comp
    ((appendDensityMap_toImage_bijective U.form).comp hi)
  have hjg (q : (U.permuteVF σ).domain) :
      (mixedVFPermutationBijection U.densityGraph.domain σ).inverse
        (mixed_vf_permutation_bijective U.densityGraph.domain σ) (f q) = g (i q) :=
    Map.inverse_apply _ _ _
  refine VFVolumeBijection.of_preserving_vf_and_density hc C f hf ?_ ?_
  · intro q
    have hv := mixed_vf_permutation_inverse_value U.domain σ q
    have hx := congrArg Prod.fst hv
    change (i q).val.1 ∘ σ = q.val.1
    funext t
    exact (congrFun hx (σ t)).trans (congrArg q.val.1 (σ.symm_apply_apply t))
  · intro q
    change U.form.value (i q) = U.densityGraph.form.value
      ((mixedVFPermutationBijection U.densityGraph.domain σ).inverse
        (mixed_vf_permutation_bijective U.densityGraph.domain σ) (f q))
    rw [hjg]
    change U.form.value (i q) = U.form.value (densityGraphProjection U.form (g (i q)))
    have h := Map.inverse_apply (appendDensityMap U.form).toImage (appendDensityMap_toImage_bijective U.form) (i q)
    exact congrArg U.form.value h.symm

end IntegrationInACVF.Section7
