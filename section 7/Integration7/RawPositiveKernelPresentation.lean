module

public import Integration7.RawVolumeKernelIdeal
public import Integration7.SurjectiveGroupificationKernels

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every raw kernel element has actual positive representatives with
identical images in the geometric common-blowup semiring. This includes
cancellation introduced by groupification, rather than assuming it away. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem raw_volume_kernel_mem_iff_positive_pair (x : RawRVVolumeRing hc C) :
    x ∈ rawVolumeKernelIdeal hc C ↔
      ∃ a b : RVVolumeIsoSemiring hc C,
        rvVolumeGradedBlowupProjection hc C a=rvVolumeGradedBlowupProjection hc C b ∧
        x=semiringGroupificationOf _ a-semiringGroupificationOf _ b := by
  exact (RingHom.mem_ker).trans
    (surjective_groupification_kernel_iff (rvVolumeGradedBlowupProjection hc C)
      (rvVolumeGradedBlowupProjection_surjective hc C) x)

theorem raw_volume_kernel_positive_pair_span :
    rawVolumeKernelIdeal hc C =
      Ideal.span {x | ∃ a b : RVVolumeIsoSemiring hc C,
        rvVolumeGradedBlowupProjection hc C a=rvVolumeGradedBlowupProjection hc C b ∧
        x=semiringGroupificationOf _ a-semiringGroupificationOf _ b} :=
  surjective_groupification_kernel_span (rvVolumeGradedBlowupProjection hc C)
    (rvVolumeGradedBlowupProjection_surjective hc C)
end IntegrationInACVF.Section7
