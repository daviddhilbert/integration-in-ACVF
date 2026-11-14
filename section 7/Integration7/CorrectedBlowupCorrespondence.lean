import Integration7.CorrectedBlowupMap
import Integration7.RVHeadJacobianComparison

/-! The corrected blowup correspondence projects to the original head
correspondence and contains the actual punctured residue vertical lines. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "K" => ModelResidue M

theorem blowupCoordinates_residue_scale (t : Fin (k + 1) → RV) (s : RV) (a : K) :
    blowupCoordinates t (s * residueRV a) =
      residueScale (blowupCoordinates t s) (Fin.snoc (fun _ : Fin k => 1) a) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [blowupCoordinates_last, residueScale, Fin.snoc_last]
    ac_rfl
  · simp only [blowupCoordinates_head, residueScale, Fin.snoc_castSucc,
      residueRV_one, mul_one]

namespace ElementaryBlowup

variable {U V WU WV : PositiveRVVolumeObject (M := M) S k}
variable (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV)

theorem correctedCorrespondence_line (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (w : WU.essential.obj.domain) (a : K) (ha : a ≠ 0) :
    productTuple (Fin.snoc (fun _ : Fin k => 1) a) (Fin.snoc (fun _ : Fin k => 1) a) ∈
      normalizedCorrespondence (volumeCorrespondence (b.correctedMap c f J)).carrier
        (WU.essential.obj.value w) (WV.essential.obj.value (b.correctedMap c f J w)) := by
  let p := b.essentialChartMap w
  let u := Map.prodFst U.essential.obj.domain (nonzeroBlowupConeSet S) p
  let s := p.val.2 0
  have hs := (mem_nonzeroBlowupConeSet S _).mp p.property.2
  let q : U.essential.obj.domain.prod (nonzeroBlowupConeSet S) :=
    ⟨(u.val, fun _ => s * residueRV a), u.property, (mem_nonzeroBlowupConeSet S _).mpr ⟨by
      change RVOperations.absoluteHom (s * residueRV a) < 1
      rw [map_mul, absolute_residue, if_neg ha, mul_one]
      exact hs.1, mul_ne_zero hs.2 ((residueRV_ne_zero a).mpr ha)⟩⟩
  let w' := b.essentialChartInverseMap q
  have hchart : b.essentialChartMap w' = q :=
    Map.apply_inverse b.essentialChartMap b.essentialChartMap_bijective q
  have hsource : WU.essential.obj.value w' =
      residueScale (WU.essential.obj.value w) (Fin.snoc (fun _ : Fin k => 1) a) := by
    rw [b.essentialChart_coordinates w', b.essentialChart_coordinates w, hchart]
    exact blowupCoordinates_residue_scale (U.essential.obj.value u) s a
  have htarget : WV.essential.obj.value (b.correctedMap c f J w') =
      residueScale (WV.essential.obj.value (b.correctedMap c f J w))
        (Fin.snoc (fun _ : Fin k => 1) a) := by
    rw [b.correctedMap_coordinates c f J w', b.correctedMap_coordinates c f J w, hchart]
    change blowupCoordinates (V.essential.obj.value (finiteIsoMap f.iso u))
      ((headCorrectionMap f J u).val 0 * (s * residueRV a)) =
      residueScale (blowupCoordinates (V.essential.obj.value (finiteIsoMap f.iso u))
        ((headCorrectionMap f J u).val 0 * s)) (Fin.snoc (fun _ : Fin k => 1) a)
    rw [← mul_assoc]
    exact blowupCoordinates_residue_scale _ _ a
  refine ⟨⟨w', ?_⟩, ?_⟩
  · change productTuple (WU.essential.obj.value w')
      (WV.essential.obj.value (b.correctedMap c f J w')) =
      residueScale (productTuple (WU.essential.obj.value w)
        (WV.essential.obj.value (b.correctedMap c f J w)))
        (productTuple (Fin.snoc (fun _ : Fin k => 1) a) (Fin.snoc (fun _ : Fin k => 1) a))
    rw [hsource, htarget]
    apply productTuple_ext <;> intro i <;>
      simp only [residueScale, productTuple_left, productTuple_right]
  · have hlin (i : Fin (k + 1)) : Fin.snoc (α := fun _ : Fin (k + 1) => K)
        (fun _ : Fin k => 1) a i ≠ 0 := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using ha
      · simp only [Fin.snoc_castSucc, ne_eq, one_ne_zero, not_false_eq_true]
    intro i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      change productTuple _ _ (productLeft (k + 1) (k + 1) j) ≠ 0
      simpa only [productTuple_left] using hlin j
    | inr j =>
      change productTuple _ _ (productRight (k + 1) (k + 1) j) ≠ 0
      simpa only [productTuple_right] using hlin j

theorem correctedCorrespondence_head (C : BaseContext M)
    {U V WU WV : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV) (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M))) :
    ∀ z ∈ (volumeCorrespondence (b.correctedMap c f J)).carrier,
      z ∘ headPairIndex k ∈
        (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f b.admissible c.admissible))).carrier := by
  rintro z ⟨w, rfl⟩
  refine ⟨Map.prodFst _ _ (b.essentialChartMap w), ?_⟩
  change productTuple
    (U.essential.obj.value (Map.prodFst _ _ (b.essentialChartMap w)) ∘ Fin.castSucc)
    (V.essential.obj.value (finiteIsoMap f.iso (Map.prodFst _ _ (b.essentialChartMap w))) ∘ Fin.castSucc) =
    productTuple (WU.essential.obj.value w) (WV.essential.obj.value (b.correctedMap c f J w)) ∘ headPairIndex k
  rw [productTuple_comp_headPairIndex, b.essentialChart_coordinates, b.correctedMap_coordinates]
  apply productTuple_ext <;> intro i <;>
    simp only [Function.comp_apply, productTuple_left, productTuple_right, blowupCoordinates_head]

end ElementaryBlowup
end IntegrationInACVF.Section7
