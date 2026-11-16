module

public import Integration7.HKZeroVolumeFamilies
public import Integration7.VolumeDensityGraphs
public import Integration7.VolumeFamilyHeadIntegrals
public import Integration7.EmptySelectedVolumeCharts
public import IntegrationSection5.GammaHeadPreparation

@[expose] public section

/-! Contracting one VF coordinate of a weighted finite-label family
creates its first volume coordinate. The density is the retained nonzero density
label of the actual VF realization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a : ℕ}

theorem ZeroVFVolumeFamily.densityGraph_label_nonzero
    (F : ZeroVFVolumeFamily C (n+1) a) :
    ∀ p ∈ F.fullVFObject.densityGraph.domain.carrier,
      (p.2 (Fin.last a)).val ≠ iRVZero := by
  intro p hp
  apply (rv_nonzero_iff_raw _).mp
  intro hz
  exact F.fullVFObject.densityGraph.form.nonzero ⟨p,hp⟩
    ((densityGraph_form_last F.fullVFObject ⟨p,hp⟩).trans hz)

def ZeroVFVolumeFamily.headIntegral
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : ZeroVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)) :
    SelectedVFVolumeFamily C n (1+T.arity) 0 :=
  nativeCoordinateVolumeFamily hc T.contractedSet
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (a+1)))
    (head_selected_fibres_finite C.uncountable.le C.saturated C.small T
      ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_map_graph T.map)
      ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_set _ (setDefinable T.target))
      Fin.elim0 (empty_selected_volume_finite _ F.fullVFObject.densityGraph.finite_labels))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a)))
    (head_retained_density_nonzero T (Fin.last a) F.densityGraph_label_nonzero)

@[simp] theorem ZeroVFVolumeFamily.headIntegral_selected
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : ZeroVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)) :
    (F.headIntegral hc Ξ T).selected 0 = 0 := rfl

def zeroFamilyHeadPreparation
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (F : ZeroVFVolumeFamily C (n+1) a) :
    HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain
  exact Classical.choose (gamma_head_preparation C.saturated C.model00 B C.small
    (generatedBaseVFField hGenerated) (Set.Subset.refl _) A
    ((gammaLogicInput B).real_set _ (setDefinable A)))

end IntegrationInACVF.Section7.HK
