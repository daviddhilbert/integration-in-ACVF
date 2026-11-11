import IntegrationSection3.AffineResidueChart
import IntegrationSection3ACVF.MaximalSubballGeometry
import Section4.ResidueScaledFunctions

/-! Native residue coordinates on the actual closed Gamma balls. The
coordinate fibres are their actual maximal open subballs, with no chosen
centre or radius added to a definability assertion. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

noncomputable section

namespace IntegrationInACVF.Section3ACVF.BallResidueChart

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Point (a : VFType (M := M)) (α : Values.Gamma (M := M)) :=
  {x : VFType (M := M) // x.val ∈ gammaBall a α false}

theorem representative_ne_zero (r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) : r ≠ 0 := by
  intro hz
  have hi : Values.vfValueHom r = Values.infinity := by
    rw [hz,map_zero]
    exact Values.infinity_eq_zero.symm
  exact α.property (hr.symm.trans hi)

def fieldPoint (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x : Point a α) :
    AffineResidueChart.closed Values.presentationValuation a r :=
  ⟨x.val,(BallKindPredicates.gammaBall_mem_valuation_closed Values.presentationValuation
    Values.presentation_compatible a r α hr x.val).mp x.property⟩

def coordinate (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x : Point a α) : ModelResidue M :=
  AffineResidueChart.chart Values.presentationValuation a r
    (representative_ne_zero r α hr) (fieldPoint a r α hr x)

theorem surjective (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) : Function.Surjective (coordinate a r α hr) := by
  intro t
  obtain ⟨x,hx⟩ := AffineResidueChart.surjective Values.presentationValuation a r
    (representative_ne_zero r α hr) t
  let p : Point a α := ⟨x.val,(BallKindPredicates.gammaBall_mem_valuation_closed
    Values.presentationValuation Values.presentation_compatible a r α hr x.val).mpr x.property⟩
  exact ⟨p,hx⟩

theorem same_fibres (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x y : Point a α) :
    coordinate a r α hr x = coordinate a r α hr y ↔
      x.val.val ∈ gammaBall y.val α true := by
  exact (AffineResidueChart.same_fibres Values.presentationValuation a r
    (representative_ne_zero r α hr) (fieldPoint a r α hr x) (fieldPoint a r α hr y)).trans
    (GammaCosetGeometry.gammaBall_mem_valuation Values.presentationValuation
      Values.presentation_compatible y.val r α hr x.val).symm

theorem fibre_set (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (b : Point a α) :
    {x : M | ∃ p : Point a α, p.val.val = x ∧ coordinate a r α hr p = coordinate a r α hr b} =
      gammaBall b.val α true := by
  ext x
  constructor
  · rintro ⟨p,rfl,he⟩
    exact (same_fibres a r α hr p b).mp he
  · intro hx
    let p : VFType (M := M) := ⟨x,hx.choose⟩
    have hpv : Values.presentationValuation (p-b.val) < Values.presentationValuation r :=
      (GammaCosetGeometry.gammaBall_mem_valuation Values.presentationValuation
        Values.presentation_compatible b.val r α hr p).mp hx
    have hpc := AffineResidueChart.open_subset_closed Values.presentationValuation a r
      (fieldPoint a r α hr b) hpv
    let q : Point a α := ⟨p,(BallKindPredicates.gammaBall_mem_valuation_closed
      Values.presentationValuation Values.presentation_compatible a r α hr p).mpr hpc⟩
    exact ⟨q,rfl,(same_fibres a r α hr q b).mpr hx⟩

end IntegrationInACVF.Section3ACVF.BallResidueChart
