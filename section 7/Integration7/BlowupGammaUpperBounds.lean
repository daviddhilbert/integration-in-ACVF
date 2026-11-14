import Integration7.EssentialGammaWeight
import Integration7.RVAbsoluteConeApproximation
import Integration7.CorrectedBlowupMap
import Integration7.IteratedVolumeBlowups

/-! Actual finite volume blowups preserve the upper cuts of absolute
Gamma weight. This is an invariant of common blowups, not groupification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "Abs" => MonoidWithZeroHom.ValueGroup₀
  (MonoidWithZeroHom.ofClass (Values.presentationValuation (M := M)))
variable {U W : PositiveRVVolumeObject (M := M) S k}

theorem ElementaryBlowup.gammaWeight_formula (b : ElementaryBlowup U W)
    (w : W.essential.obj.domain) :
    essentialGammaWeight W w = RVOperations.absoluteHom ((b.essentialChartMap w).val.2 0) *
      essentialGammaWeight U (Map.prodFst _ _ (b.essentialChartMap w)) := by
  unfold IntegrationInACVF.Section7.essentialGammaWeight
  rw [b.essentialChart_density,b.essentialChart_coordinates,blowupCoordinates_absolute_product]
  ac_rfl

theorem ElementaryBlowup.essentialGammaUpperBound (b : ElementaryBlowup U W)
    (a : Abs) (ha : a ≠ 0) : essentialGammaUpperBound U a ↔ essentialGammaUpperBound W a := by
  constructor
  · intro h w
    rw [b.gammaWeight_formula]
    have hs := ((mem_nonzeroBlowupConeSet S _).mp (b.essentialChartMap w).property.2).1
    exact (mul_le_of_le_one_left zero_le hs.le).trans (h _)
  · intro h u
    by_contra hn
    have hu : a < essentialGammaWeight U u := lt_of_not_ge hn
    obtain ⟨s,hs0,hs1,hsu⟩ := exists_absolute_cone_factor a (essentialGammaWeight U u) ha hu
    let p : U.essential.obj.domain.prod (nonzeroBlowupConeSet S) :=
      ⟨(u.val,fun _ => s),u.property,(mem_nonzeroBlowupConeSet S _).mpr ⟨hs1,hs0⟩⟩
    obtain ⟨w,hw⟩ := b.essentialChartMap_bijective.2 p
    have hwu : Map.prodFst _ _ (b.essentialChartMap w) = u :=
      Subtype.ext (congrArg (fun z : U.essential.obj.domain.prod (nonzeroBlowupConeSet S) => z.val.1) hw)
    have hws : (b.essentialChartMap w).val.2 0 = s :=
      congrArg (fun z : U.essential.obj.domain.prod (nonzeroBlowupConeSet S) => z.val.2 0) hw
    have hh := h w
    rw [b.gammaWeight_formula,hwu,hws] at hh
    exact (not_le_of_gt hsu) hh

theorem VolumeBlowup.essentialGammaUpperBound (b : VolumeBlowup U W)
    (a : Abs) (ha : a ≠ 0) : essentialGammaUpperBound U a ↔ essentialGammaUpperBound W a := by
  rw [b.sourceIso.essentialGammaUpperBound, b.targetIso.essentialGammaUpperBound,
    essentialGammaUpperBound_coprod,essentialGammaUpperBound_coprod,
    b.elementary.essentialGammaUpperBound a ha]

theorem IteratedVolumeBlowup.essentialGammaUpperBound {n : ℕ}
    (b : IteratedVolumeBlowup n U W) (a : Abs) (ha : a ≠ 0) :
    essentialGammaUpperBound U a ↔ essentialGammaUpperBound W a := by
  induction b with
  | refl => rfl
  | step b rest ih => exact b.some.essentialGammaUpperBound a ha |>.trans ih

theorem VolumeBlowupEquivalent.essentialGammaUpperBound
    (b : VolumeBlowupEquivalent U W) (a : Abs) (ha : a ≠ 0) :
    essentialGammaUpperBound U a ↔ essentialGammaUpperBound W a := by
  obtain ⟨m,n,U',W',hU,hW,⟨e⟩⟩ := b
  exact (hU.essentialGammaUpperBound a ha).trans
    ((e.essentialGammaUpperBound a).trans (hW.essentialGammaUpperBound a ha).symm)
end IntegrationInACVF.Section7
