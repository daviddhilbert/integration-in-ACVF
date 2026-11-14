import Integration7.CorrectedBlowupCorrespondence

/-! Identification of a defined corrected Jacobian with the density ratio.
Generic existence and the dimension of the head exception are handled
separately when constructing the volume isomorphism. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.ElementaryBlowup

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem correctedJacobian_eq_volumeRatio (C : BaseContext M)
    {U V WU WV : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV) (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (w : WU.essential.obj.domain)
    (hJ : IsRVJacobianAt
      (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f b.admissible c.admissible))).carrier
      (U.essential.obj.value (Map.prodFst _ _ (b.essentialChartMap w)) ∘ Fin.castSucc)
      (V.essential.obj.value (finiteIsoMap f.iso (Map.prodFst _ _ (b.essentialChartMap w))) ∘ Fin.castSucc)
      ((J (Map.prodFst _ _ (b.essentialChartMap w))).val 0))
    {ω : CanonicalRV.RVSort M}
    (hfull : IsRVJacobianAt (volumeCorrespondence (finiteIsoMap (b.correctedIso c f J))).carrier
      (WU.essential.obj.value w) (WV.essential.obj.value (finiteIsoMap (b.correctedIso c f J) w)) ω) :
    ω = volumeRatio WU WV (b.correctedIso c f J) w := by
  let u := Map.prodFst _ _ (b.essentialChartMap w)
  let s := (b.essentialChartMap w).val.2 0
  let r := U.essential.obj.value u (Fin.last k)
  let t := V.essential.obj.value (finiteIsoMap f.iso u) (Fin.last k)
  let d := headCorrection f u ((J u).val 0)
  have hs : s ≠ 0 := ((mem_nonzeroBlowupConeSet _ _).mp (b.essentialChartMap w).property.2).2
  have hr : r ≠ 0 := (rv_nonzero_iff_raw _).mpr (U.essential_nonzero u (Fin.last k))
  have ht : t ≠ 0 := (rv_nonzero_iff_raw _).mpr (V.essential_nonzero (finiteIsoMap f.iso u) (Fin.last k))
  have hhead : IsRVJacobianAt
      (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f b.admissible c.admissible))).carrier
      (WU.essential.obj.value w ∘ Fin.castSucc)
      (WV.essential.obj.value (b.correctedMap c f J w) ∘ Fin.castSucc) ((J u).val 0) := by
    simpa only [b.essentialChart_coordinates, b.correctedMap_coordinates, Function.comp_def,
      blowupCoordinates_head] using hJ
  have he := rvJacobian_eq_head_mul_last_ratio
    (correctedCorrespondence_head C b c f J) (b.correctedCorrespondence_line c f J w) hfull hhead
  have hc := headCorrectionMap_of_jacobian C f b.admissible c.admissible J u hJ
  change ω = (J u).val 0 *
    (WV.essential.obj.value (b.correctedMap c f J w) (Fin.last k) /
      WU.essential.obj.value w (Fin.last k)) at he
  rw [b.correctedMap_coordinates, b.essentialChart_coordinates,
    blowupCoordinates_last, blowupCoordinates_last, hc] at he
  have hquot : ((d * s) * t) / (s * r) = d * (t / r) := by
    calc
      ((d * s) * t) / (s * r) = (s * (d * t)) / (s * r) := by ac_rfl
      _ = (d * t) / r := mul_div_mul_left _ _ hs
      _ = d * (t / r) := by simp only [div_eq_mul_inv, mul_assoc]
  change ω = (J u).val 0 * (((d * s) * t) / (s * r)) at he
  rw [hquot] at he
  have hcancel : d * ((J u).val 0 * (t / r)) =
      U.essentialForm.value u / V.essentialForm.value (finiteIsoMap f.iso u) :=
    blowupCorrection_cancel _ _ _ _ _ (rvJacobian_ne_zero hJ) hr ht
  have hratio : volumeRatio WU WV (b.correctedIso c f J) w =
      U.essentialForm.value u / V.essentialForm.value (finiteIsoMap f.iso u) := by
    change WU.essentialForm.value w / WV.essentialForm.value (b.correctedMap c f J w) = _
    rw [b.essentialChart_density, b.correctedMap_density]
  exact he.trans ((show (J u).val 0 * (d * (t / r)) = d * ((J u).val 0 * (t / r)) by
    ac_rfl).trans (hcancel.trans hratio.symm))

end IntegrationInACVF.Section7.ElementaryBlowup
