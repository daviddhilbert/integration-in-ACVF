import Integration7.PullbackCoordinateVolumeObjects
import Integration7.EssentialEmptyVolumeIsomorphisms
import Integration7.CommonContextVolumeEquivalences

/-! Empty mixed domains have empty essential pullback volume objects;
these supply the base case of finite volume partition gluing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a : ℕ}

theorem pullback_volume_essential_empty
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S (n+1) a)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ S _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hEmpty : carrier A = ∅) :
    (pullbackCoordinateVolumeObject hc A hAF δ hδ).essential.obj.domain.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hFull := rvEssentialLabels_subset (pullbackCoordinateVolumeObject hc A hAF δ hδ).underlying.obj hr
  obtain ⟨p,hp⟩ := hFull
  exact (Set.eq_empty_iff_forall_notMem.mp hEmpty p.val) p.property

theorem CommonContextVolumeEquivalent.of_empty_essential
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : GammaVolumeObjects G (C.base : Set M) n)
    (hU : U.val.essential.obj.domain.carrier = ∅) (hV : V.val.essential.obj.domain.carrier = ∅) :
    CommonContextVolumeEquivalent G C U V := by
  let e := RVVolumeIso.of_essential_empty hc C U.val V.val hU hV
  exact CommonContextVolumeEquivalent.of_iso e (gamma_volume_iso_of_essential_empty e hU)

end IntegrationInACVF.Section7
