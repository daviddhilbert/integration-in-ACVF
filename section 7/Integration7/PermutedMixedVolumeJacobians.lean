module

public import Integration7.VFPermutationJacobians
public import Integration7.NativeVolumeDomains
public import IntegrationSection6.GammaPermutedUnaryMaps

@[expose] public section

/-! The native simultaneous VF permutation transports an actual fixed-label
mixed Jacobian chart with the same determinant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}

set_option maxHeartbeats 2400000 in
theorem mixed_vf_jacobian_conjugate_permutation
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}
    (f : Map U V) (σ : Equiv.Perm (Fin n))
    (p : vfPermutationImage U σ) (J : VFType (M := M))
    (hJ : HasMixedVFJacobianAt (rawSpecialMap hc f)
      (Map.inverse (vfPermutationBijection U σ) (vfPermutationBijection_bijective U σ) p) J) :
    HasMixedVFJacobianAt (rawSpecialMap hc (vfPermutedMap f σ)) p J := by
  let P := vfPermutationBijection U σ
  let hP := vfPermutationBijection_bijective U σ
  let q := Map.inverse P hP p
  have hqp : P q = p := Map.apply_inverse P hP p
  have hVF : q.val.1 ∘ σ = p.val.1 := congrArg (fun z => z.val.1) hqp
  have hRV : q.val.2 = p.val.2 := congrArg (fun z => z.val.2) hqp
  obtain ⟨F,⟨ρ,hChart⟩,hJac⟩ := hJ
  let G : (Fin n → VFType (M := M)) → Fin n → VFType (M := M) := fun y => F (y ∘ σ.symm) ∘ σ
  refine ⟨G,⟨ρ,fun y hy => ?_⟩,?_⟩
  · have hy' : y ∘ σ.symm ∈ vfBall q.val.1 ρ := by
      intro i
      have hh := hy (σ.symm i)
      have hi := congrFun hVF (σ.symm i)
      change q.val.1 (σ (σ.symm i)) = p.val.1 (σ.symm i) at hi
      rw [σ.apply_symm_apply] at hi
      simpa only [Function.comp_apply,hi] using hh
    obtain ⟨hSource,hOutput⟩ := hChart (y ∘ σ.symm) hy'
    let u : U := ⟨(y ∘ σ.symm,q.val.2),hSource⟩
    have hU : (y,p.val.2) ∈ carrier (vfPermutationImage U σ) := by
      apply (vfPermutationImage_row U σ y p.val.2).mpr
      exact hRV ▸ hSource
    let u' : vfPermutationImage U σ := ⟨(y,p.val.2),hU⟩
    have hPu : P u = u' := by
      apply Subtype.ext
      refine Prod.ext ?_ hRV
      funext j
      change y (σ.symm (σ j)) = y j
      rw [σ.symm_apply_apply]
    have hInv : Map.inverse P hP u' = u := by rw [← hPu]; exact Map.inverse_apply P hP u
    refine ⟨hU,?_⟩
    change (vfPermutation σ (f (Map.inverse P hP u')).val) =
      (G y,(vfPermutedMap f σ p).val.2)
    rw [hInv]
    exact congrArg (vfPermutation σ) hOutput
  · have hj := vf_jacobian_conjugate_permutation hJac σ
    exact Eq.mp (congrArg (fun z => HasVFJacobianAt G z J) hVF) hj

end IntegrationInACVF.Section7
