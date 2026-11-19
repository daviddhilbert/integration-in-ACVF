import Integration7.GammaNamedCoproductLifts
import Integration7.GammaElementaryBlowupPartitions
import Integration7.VolumeBlowupLiftInvariance

/-! **Gamma-named Proposition 7.9 (positive degree).** Over the Gamma-named
base `⟨C.base, Ξ⟩` (VF-Gamma generated), with objects coded over the named
code context, the lift is well defined on Gamma blowup classes and is a
bijection onto Gamma VF volume classes:

* Gamma blowups, iterated blowups and blowup equivalences have Gamma VF
  lifts (Gamma Theorem 9.16 for the isomorphisms, Section 6 focus lifts for
  elementary blowups);
* `gammaNamedVolumeLiftOnClasses` is the induced map of class sets;
* it is injective (forward Proposition 7.8) and surjective. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {k : ℕ}

namespace GammaNamed
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (hGC : G.real ⊆ (C.base : Set M)) (hGenerated : VFGammaGeneratedBase G)
include hc hGC hGenerated

theorem elementary_blowup_lift_iso_gamma
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : ElementaryBlowup U W)
    (hU : VolumeObjectGamma U G) (hW : VolumeObjectGamma W G)
    (hFull : RVMapGamma b.packedChartMap G) (hCenter : GammaBlowupCenter U G) :
    ∃ f : VFVolumeIso (rvVolumeLift U) (rvVolumeLift W), f.GammaDefinable G := by
  obtain ⟨f, hf⟩ := elementary_volume_lift_iso_gamma hc C hGC hGenerated U hU b.admissible hCenter
  obtain ⟨e, he⟩ := ElementaryBlowup.exists_gamma_canonical_iso hc C b hU hW hFull
  obtain ⟨g, hg⟩ := rv_volume_iso_lift_gamma hc C hGC hGenerated
    (VolumeObjectGamma.elementary_canonical hc C U hU b.admissible) hW e he
  exact ⟨f.trans hc C g, hf.trans hc C hg⟩

theorem volume_blowup_lift_iso_gamma
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U G) (hV : VolumeObjectGamma V G)
    (b : VolumeBlowup U V) (hb : b.GammaDefinable G) :
    ∃ f : VFVolumeIso (rvVolumeLift U) (rvVolumeLift V), f.GammaDefinable G := by
  obtain ⟨e, he⟩ := elementary_blowup_lift_iso_gamma hc C hGC hGenerated b.elementary hb.locus hb.blown
    hb.elementary hb.centerAlgebraic
  obtain ⟨s, hs⟩ := rv_volume_iso_lift_gamma hc C hGC hGenerated hU (hb.locus.coprod hb.complement)
    b.sourceIso hb.source
  obtain ⟨t, ht⟩ := rv_volume_iso_lift_gamma hc C hGC hGenerated hV (hb.blown.coprod hb.complement)
    b.targetIso hb.target
  let F := e.coprod hc C (VFVolumeIso.refl hc C (rvVolumeLift b.complement))
  have hF : F.GammaDefinable G :=
    VFVolumeIso.GammaDefinable.coprod hc C he
      ((rv_volume_lift_gamma hc C hGC hb.complement).refl_iso hc C)
  have hl := volume_lift_coprod_iso_gamma hc C hGC hb.locus hb.complement
  have hr := volume_lift_coprod_iso_gamma hc C hGC hb.blown hb.complement
  exact ⟨s.trans hc C (((volumeLiftCoprodIso hc C b.locus b.complement).symm hc C).trans hc C
      (F.trans hc C ((volumeLiftCoprodIso hc C b.blownLocus b.complement).trans hc C (t.symm hc C)))),
    hs.trans hc C ((hl.symm hc C).trans hc C (hF.trans hc C (hr.trans hc C (ht.symm hc C))))⟩

theorem iterated_blowup_lift_iso_gamma {m : ℕ} {U V : GammaVolumeObjects G (C.base : Set M) k}
    (h : GammaIteratedVolumeBlowup G (C.base : Set M) k m U V) :
    ∃ f : VFVolumeIso (rvVolumeLift U.val) (rvVolumeLift V.val), f.GammaDefinable G := by
  induction h with
  | refl U =>
    exact ⟨VFVolumeIso.refl hc C _, (rv_volume_lift_gamma hc C hGC U.property).refl_iso hc C⟩
  | @step n U V W hb h ih =>
    obtain ⟨b, hbΓ⟩ := hb
    obtain ⟨f, hf⟩ := volume_blowup_lift_iso_gamma hc C hGC hGenerated U.property V.property b hbΓ
    obtain ⟨g, hg⟩ := ih
    exact ⟨f.trans hc C g, hf.trans hc C hg⟩

theorem blowup_equivalent_lift_iso_gamma {U V : GammaVolumeObjects G (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent G (C.base : Set M) k U V) :
    ∃ f : VFVolumeIso (rvVolumeLift U.val) (rvVolumeLift V.val), f.GammaDefinable G := by
  obtain ⟨m, n, P, Q, hP, hQ, e, he⟩ := h
  obtain ⟨f, hf⟩ := iterated_blowup_lift_iso_gamma hc C hGC hGenerated hP
  obtain ⟨g, hg⟩ := iterated_blowup_lift_iso_gamma hc C hGC hGenerated hQ
  obtain ⟨j, hj⟩ := rv_volume_iso_lift_gamma hc C hGC hGenerated P.property Q.property e he
  exact ⟨f.trans hc C (j.trans hc C (g.symm hc C)), hf.trans hc C (hj.trans hc C (hg.symm hc C))⟩

end GammaNamed

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

/-- Well-definedness of the lift on Gamma-named blowup classes. -/
theorem gamma_named_lift_class_eq_of_blowup_class_eq
    (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
    (U V : GammaVolumeObjects (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M) k)
    (h : gammaVolumeBlowupClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) U =
      gammaVolumeBlowupClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) V) :
    gammaVFVolumeClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
        (gammaVolumeLift hc (gammaNamedCodeContext C Ξ hΞ) (fun _ h => gamma_named_code_context_base C Ξ hΞ h) U) =
      gammaVFVolumeClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
        (gammaVolumeLift hc (gammaNamedCodeContext C Ξ hΞ) (fun _ h => gamma_named_code_context_base C Ξ hΞ h) V) := by
  obtain ⟨f, hf⟩ := GammaNamed.blowup_equivalent_lift_iso_gamma hc (gammaNamedCodeContext C Ξ hΞ)
    (fun _ h => gamma_named_code_context_base C Ξ hΞ h) hGenerated
    ((gammaVolumeBlowupClass_eq_iff hc _ _).mp h)
  exact (gammaVFVolumeClass_eq_iff hc _ _).mpr ⟨f, hf⟩

/-- The lift on Gamma-named positive-degree blowup classes. -/
def gammaNamedVolumeLiftOnClasses (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ)) :
    GammaVolumeBlowupClasses hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) k →
      GammaVFVolumeClasses hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) k :=
  Quotient.lift (fun U => gammaVFVolumeClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
      (gammaVolumeLift hc (gammaNamedCodeContext C Ξ hΞ) (fun _ h => gamma_named_code_context_base C Ξ hΞ h) U))
    (fun U V h => gamma_named_lift_class_eq_of_blowup_class_eq hc C Ξ hΞ hGenerated U V
      ((gammaVolumeBlowupClass_eq_iff hc _ _).mpr h))

@[simp] theorem gammaNamedVolumeLiftOnClasses_class (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
    (U : GammaVolumeObjects (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M) k) :
    gammaNamedVolumeLiftOnClasses hc C Ξ hΞ hGenerated
        (gammaVolumeBlowupClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) U) =
      gammaVFVolumeClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
        (gammaVolumeLift hc (gammaNamedCodeContext C Ξ hΞ) (fun _ h => gamma_named_code_context_base C Ξ hΞ h) U) := rfl

/-- **Gamma-named Proposition 7.9 (positive degree).** The lift is a bijection from Gamma-named
RV blowup classes onto Gamma-named VF volume classes. -/
theorem gamma_named_volume_lift_on_classes_bijective
    (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    Function.Bijective (gammaNamedVolumeLiftOnClasses (k := k) hc C Ξ hΞ hGenerated) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    rename_i U V
    exact gamma_named_blowup_class_eq_of_lift_class_eq hc C Ξ hΞ hGenerated γ hγ hγ1 U V hxy
  · intro y
    induction y using Quotient.inductionOn
    rename_i A
    obtain ⟨U, hU⟩ := gamma_named_lift_class_surjective hc C Ξ hΞ hGenerated A
    exact ⟨gammaVolumeBlowupClass hc _ _ U, hU.symm⟩

end IntegrationInACVF.Section7
