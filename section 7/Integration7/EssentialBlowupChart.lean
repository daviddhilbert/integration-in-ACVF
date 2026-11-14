import Integration7.ElementaryBlowupConstruction
import Integration7.RVVolumeMorphisms
import Integration7.NonzeroConeScaling
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7.ElementaryBlowup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U W : PositiveRVVolumeObject (M := M) S k} (b : ElementaryBlowup U W)

theorem essential_mem_iff (w : W.underlying.obj.domain) :
    w.val ∈ W.essential.obj.domain.carrier ↔
      (b.projection w).val ∈ U.essential.obj.domain.carrier ∧ (b.parameter w).val 0 ≠ 0 := by
  change w.val ∈ (rvEssentialLabels W.underlying.obj).carrier ↔
    (b.projection w).val ∈ (rvEssentialLabels U.underlying.obj).carrier ∧ (b.parameter w).val 0 ≠ 0
  rw [mem_rvEssentialLabels W.underlying.obj w,
    mem_rvEssentialLabels U.underlying.obj (b.projection w)]
  constructor
  · intro hW
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact (rv_nonzero_iff_raw _).mp (b.admissible.nonzero _)
      · change (U.underlying.obj.value (Map.prodFst _ _ (b.chartMap w)) j.castSucc).val ≠ iRVZero
        rw [← b.head w j]
        exact hW j.castSucc
    · intro hp
      exact ((rv_nonzero_iff_raw _).mpr (hW (Fin.last k))) ((b.last_eq_zero_iff w).mpr hp)
  · rintro ⟨hU, hp⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · apply (rv_nonzero_iff_raw _).mp
      rw [b.last]
      exact mul_ne_zero hp ((rv_nonzero_iff_raw _).mpr (hU (Fin.last k)))
    · rw [b.head]
      exact hU j.castSucc

def essentialChartMap : Map W.essential.obj.domain
    (U.essential.obj.domain.prod (nonzeroBlowupConeSet S)) :=
  (b.chartMap.restrict (A' := W.essential.obj.domain)
    (rvEssentialLabels_subset W.underlying.obj)).corestrict (by
    intro w
    let w0 : W.underlying.obj.domain := ⟨w.val, rvEssentialLabels_subset W.underlying.obj w.property⟩
    have hw := (b.essential_mem_iff w0).mp w.property
    refine ⟨hw.1, ?_⟩
    exact (mem_nonzeroBlowupConeSet S _).mpr ⟨b.parameter_mem w0, hw.2⟩)

theorem essentialChartMap_bijective : Function.Bijective b.essentialChartMap := by
  constructor
  · intro w z he
    let w0 : W.underlying.obj.domain := ⟨w.val, rvEssentialLabels_subset W.underlying.obj w.property⟩
    let z0 : W.underlying.obj.domain := ⟨z.val, rvEssentialLabels_subset W.underlying.obj z.property⟩
    have he' : b.chartMap w0 = b.chartMap z0 := Subtype.ext
      (congrArg (fun p : U.essential.obj.domain.prod (nonzeroBlowupConeSet S) => p.val) he)
    exact Subtype.ext (congrArg (fun p : W.underlying.obj.domain => p.val) (b.chartMap_bijective.1 he'))
  · intro y
    let y' : U.underlying.obj.domain.prod (blowupConeSet S) :=
      ⟨y.val, rvEssentialLabels_subset U.underlying.obj y.property.1, (nonzeroBlowupConeSet_subset S y.property.2)⟩
    obtain ⟨w, hw⟩ := b.chartMap_bijective.2 y'
    have hp : (b.projection w).val = y.val.1 :=
      congrArg (fun p : U.underlying.obj.domain.prod (blowupConeSet S) => p.val.1) hw
    have ht : (b.parameter w).val 0 = y.val.2 0 :=
      congrArg (fun p : U.underlying.obj.domain.prod (blowupConeSet S) => p.val.2 0) hw
    have hwe : w.val ∈ W.essential.obj.domain.carrier := (b.essential_mem_iff w).mpr ⟨by
      rw [hp]
      exact y.property.1, by
      rw [ht]
      exact ((mem_nonzeroBlowupConeSet S _).mp y.property.2).2⟩
    exact ⟨⟨w.val, hwe⟩, Subtype.ext
      (congrArg (fun p : U.underlying.obj.domain.prod (blowupConeSet S) => p.val) hw)⟩

def essentialChartInverseMap :
    Map (U.essential.obj.domain.prod (nonzeroBlowupConeSet S)) W.essential.obj.domain :=
  b.essentialChartMap.inverse b.essentialChartMap_bijective

theorem essentialChart_coordinates (w : W.essential.obj.domain) :
    W.essential.obj.value w =
      blowupCoordinates
        (U.essential.obj.value (Map.prodFst _ _ (b.essentialChartMap w)))
        ((b.essentialChartMap w).val.2 0) := by
  funext i
  let w0 : W.underlying.obj.domain := ⟨w.val, rvEssentialLabels_subset W.underlying.obj w.property⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [blowupCoordinates_last]
    exact b.last w0
  · rw [blowupCoordinates_head]
    exact b.head w0 j

theorem essentialChart_density (w : W.essential.obj.domain) :
    W.essentialForm.value w =
      U.essentialForm.value (Map.prodFst _ _ (b.essentialChartMap w)) :=
  b.volume ⟨w.val, rvEssentialLabels_subset W.underlying.obj w.property⟩
end IntegrationInACVF.Section7.ElementaryBlowup
