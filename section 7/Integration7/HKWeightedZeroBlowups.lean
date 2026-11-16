module

public import Integration7.HKRVVolumeProducts
public import Integration7.ElementaryZeroVolumeProducts

@[expose] public section

/-! Elementary volume blowups commute with a weighted zero factor.
The scalar density is pulled back on both sides of the same chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

set_option allowUnsafeReducibility true in
attribute [local reducible] zeroProduct multiplyForm PositiveRVVolumeObject.zero_prod rvFiniteProductObject

def weightedZeroElementary {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (Z : ZeroRVVolumeObject (M := M) S) :
    ElementaryBlowup (zeroProduct Z U) (zeroProduct Z W) where
  admissible := {
    nonzero := (b.admissible.zero_product Z.underlying).nonzero
    algebraic := (b.admissible.zero_product Z.underlying).algebraic }
  chartMap := b.zeroProductChart Z.underlying
  chartMap_bijective := b.zeroProductChart_bijective Z.underlying
  head x i := (congrFun (b.zeroProductChart_coordinates Z.underlying x) i.castSucc).trans
    (blowupCoordinates_head _ _ i)
  last x := (congrFun (b.zeroProductChart_coordinates Z.underlying x) (Fin.last k)).trans
    (blowupCoordinates_last _ _)
  volume x := by
    obtain ⟨z,w,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain W.underlying.obj.domain x
    rw [b.zeroProductChart_pair]
    change (zeroProduct Z W).form.value _ =
      (zeroProduct Z U).form.value (rvPackPair _ _ z (b.projection w))
    rw [zeroProduct_density, zeroProduct_density, rvUnpack_pair, rvUnpack_pair, b.volume]
    rfl

end IntegrationInACVF.Section7.HK
