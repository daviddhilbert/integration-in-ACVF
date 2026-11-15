import Integration7.MixedVFProductCharts

/-! The actual mixed Jacobian of a Cartesian product map is the
product of the original two mixed Jacobians, with the original VF order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}
variable {U U' : PositiveVFVolumeObject (M := M) S n} {V V' : PositiveVFVolumeObject (M := M) S m}

theorem has_mixed_vf_jacobian_product
    (f : Map U.domain U'.domain) (g : Map V.domain V'.domain) (u : U.domain) (v : V.domain)
    (J K : VFType (M := M)) (hf : HasMixedVFJacobianAt f u J) (hg : HasMixedVFJacobianAt g v K) :
    HasMixedVFJacobianAt (positiveVFVolumeProductMap f g)
      ((mixedPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩) (J*K) := by
  obtain ⟨F,hF,hJF⟩ := hf
  obtain ⟨G,hG,hJG⟩ := hg
  exact ⟨tupleBlockProduct (n := n+1) (m := m+1) F G,is_vf_chart_at_product f g u v F G hF hG,
    has_vf_jacobian_block_product (n := n+1) (m := m+1) F G u.val.1 v.val.1 J K hJF hJG⟩

end IntegrationInACVF.Section7
