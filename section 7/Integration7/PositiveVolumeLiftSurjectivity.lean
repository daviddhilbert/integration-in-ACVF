module

public import Integration7.PositiveBlowupLiftClasses
public import Integration7.SpecialPullbackVolumeObjects
public import Integration7.RawPullbackVolumeLifts
public import Integration7.VolumeDensityGraphs
public import Integration7.NativeRVGraphVolumeRefinements
public import Section5.Surjectivity

@[expose] public section

/-! Every actual positive VF volume object is the full volume lift of
an actual finite RV volume object, up to a genuine full volume bijection.
The density graph and special preparation keep arbitrary densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (carrier VF RV)
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem positive_volume_lift_bijection_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) :
    ∃ P : PositiveRVVolumeObject (M := M) (C.base : Set M) k,
      Nonempty (VFVolumeBijection U (rvVolumeLift P)) := by
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  obtain ⟨b,B,⟨T⟩,hBP⟩ := SpecialTransformations.Section5.Paper.corollary_5_6 C.saturated C.model00 C.small A
  let δ := Fin.last U.arity
  have hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := by
    intro p
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact U.densityGraph.form.nonzero ⟨p.val,p.property⟩
      ((densityGraph_form_last U ⟨p.val,p.property⟩).trans hz)
  have hfinB := special_target_finite_labels C ∅ T U.densityGraph.finite_labels
  have hBF := special_pullback_volume_finite C ∅ T hBP U.densityGraph.finite_labels
  let ε := suffixIndex (special_chain_rvArity_le T.chain) δ
  have hε := special_retained_density_nonzero T δ hδ
  let P := pullbackCoordinateVolumeObject hc B hBF ε hε
  let ψ := rawPullbackVolumeForm hc B hBP hBF ε hε
  let W := nativeMixedVFVolumeObject hc B hfinB ψ
  have hDensity : ∀ p, U.densityGraph.form.value p = ψ.value (rawSpecialMap hc T.toMap p) := by
    intro p
    rw [densityGraph_form_last,rawPullbackVolumeForm_density]
    exact (special_oldLabels T ⟨p.val,p.property⟩ δ).symm
  let f : VFVolumeBijection U.densityGraph W := ⟨rawSpecialMap hc T.toMap,T.bijective,
    (special_preserves_volume hc C (Nat.zero_lt_succ k) T U.densityGraph.form ψ hDensity).1⟩
  let g : VFVolumeBijection W (rvVolumeLift P) := ⟨rawPullbackVolumeLiftMap hc B hBP,
    rawPullbackVolumeLiftMap_bijective hc B hBP,rawPullbackVolumeLiftMap_preserves hc C B hBP hBF ε hε⟩
  exact ⟨P,⟨(volumeDensityGraphBijection hc C U).trans hc C (f.trans hc C g)⟩⟩

theorem positive_volume_lift_on_blowup_classes_surjective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) :
    Function.Surjective (positiveVolumeLiftOnBlowupClasses hc C k Ξ hGenerated) := by
  intro a
  induction a using Quotient.inductionOn with
  | h U =>
    obtain ⟨P,⟨f⟩⟩ := positive_volume_lift_bijection_exists hc C U
    refine ⟨positiveVolumeBlowupClass hc C P,?_⟩
    exact (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨(VFVolumeIso.of_bijection f).symm hc C⟩

end IntegrationInACVF.Section7
