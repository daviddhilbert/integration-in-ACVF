import Integration7.ElementaryVolumeProducts
import Integration7.ZeroFactorVolumeObjects
import Integration7.VolumeProductPointwise
import IntegrationSection6.ElementaryRightProduct

/-! Multiplying an elementary volume blowup by an ordinary RV[0] factor
retains the distinguished coordinate and density on the positive factor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.zero_prod rvFiniteProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem BlowupAdmissible.zero_product {U : PositiveRVVolumeObject (M := M) S k}
    (h : BlowupAdmissible U) (Z : RVFiniteObject (M := M) S 0) :
    BlowupAdmissible (PositiveRVVolumeObject.zero_prod Z U) := by
  have hc (z : Z.obj.domain) (u : U.underlying.obj.domain) :
      (PositiveRVVolumeObject.zero_prod Z U).underlying.obj.value
        (rvPackPair Z.obj.domain U.underlying.obj.domain z u) = U.underlying.obj.value u := by
    rw [zeroPositiveProduct_coordinates,rvUnpack_pair]
    rfl
  constructor
  · intro x
    obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.obj.domain U.underlying.obj.domain x
    rw [hc]
    exact h.nonzero u
  · intro x
    obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.obj.domain U.underlying.obj.domain x
    rw [hc]
    exact h.algebraic u

def ElementaryBlowup.zeroProductChart {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (Z : RVFiniteObject (M := M) S 0) :
    Map (PositiveRVVolumeObject.zero_prod Z W).underlying.obj.domain
      ((PositiveRVVolumeObject.zero_prod Z U).underlying.obj.domain.prod (blowupConeSet S)) :=
  ((Map.prodMap (rvPack Z.obj.domain U.underlying.obj.domain).toImage
    (Map.id (blowupConeSet S))).comp
      ((Map.prodAssoc Z.obj.domain U.underlying.obj.domain (blowupConeSet S)).inverse
        (Map.prodAssoc_bijective _ _ _))).comp
    ((Map.prodMap (Map.id Z.obj.domain) b.chartMap).comp
      (rvUnpack Z.obj.domain W.underlying.obj.domain))

theorem ElementaryBlowup.zeroProductChart_bijective {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (Z : RVFiniteObject (M := M) S 0) :
    Function.Bijective (b.zeroProductChart Z) :=
  ((Map.prodMap_bijective _ _ (rvPackToImage_bijective _ _) Function.bijective_id).comp
    (Section6.mapInverse_bijective _ (Map.prodAssoc_bijective _ _ _))).comp
    ((Map.prodMap_bijective _ _ Function.bijective_id b.chartMap_bijective).comp
      (rvUnpack_bijective _ _))

theorem ElementaryBlowup.zeroProductChart_pair {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (Z : RVFiniteObject (M := M) S 0)
    (r : Z.obj.domain) (w : W.underlying.obj.domain) :
    b.zeroProductChart Z (rvPackPair Z.obj.domain W.underlying.obj.domain r w) =
      ⟨((rvPackPair Z.obj.domain U.underlying.obj.domain r (b.projection w)).val,
        (b.parameter w).val),
        (rvPackPair Z.obj.domain U.underlying.obj.domain r (b.projection w)).property,
        (b.parameter w).property⟩ := by
  have h := Map.inverse_apply
    (Map.prodAssoc Z.obj.domain U.underlying.obj.domain (blowupConeSet S))
    (Map.prodAssoc_bijective _ _ _)
    ⟨((r.val,(b.projection w).val),(b.parameter w).val),
      ⟨r.property,(b.projection w).property⟩,(b.parameter w).property⟩
  simp only [ElementaryBlowup.zeroProductChart,Map.comp_apply,rvUnpack_pair]
  change (Map.prodMap (rvPack Z.obj.domain U.underlying.obj.domain).toImage
    (Map.id (blowupConeSet S)))
    ((Map.prodAssoc Z.obj.domain U.underlying.obj.domain (blowupConeSet S)).inverse
      (Map.prodAssoc_bijective _ _ _)
      (Map.prodAssoc Z.obj.domain U.underlying.obj.domain (blowupConeSet S)
        ⟨((r.val,(b.projection w).val),(b.parameter w).val),
          ⟨r.property,(b.projection w).property⟩,(b.parameter w).property⟩)) = _
  rw [h]
  rfl

theorem ElementaryBlowup.zeroProductChart_coordinates {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (Z : RVFiniteObject (M := M) S 0)
    (x : (PositiveRVVolumeObject.zero_prod Z W).underlying.obj.domain) :
    (PositiveRVVolumeObject.zero_prod Z W).underlying.obj.value x = blowupCoordinates
      ((PositiveRVVolumeObject.zero_prod Z U).underlying.obj.value (Map.prodFst _ _ (b.zeroProductChart Z x)))
      ((b.zeroProductChart Z x).val.2 0) := by
  obtain ⟨z,w,rfl⟩ := exists_rvPackPair Z.obj.domain W.underlying.obj.domain x
  rw [b.zeroProductChart_pair]
  change (PositiveRVVolumeObject.zero_prod Z W).underlying.obj.value _ = blowupCoordinates
    ((PositiveRVVolumeObject.zero_prod Z U).underlying.obj.value (rvPackPair _ _ z (b.projection w))) _
  rw [zeroPositiveProduct_coordinates,zeroPositiveProduct_coordinates,rvUnpack_pair,rvUnpack_pair]
  exact b.coordinates w

def ElementaryBlowup.zero_product {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (Z : RVFiniteObject (M := M) S 0) :
    ElementaryBlowup (PositiveRVVolumeObject.zero_prod Z U) (PositiveRVVolumeObject.zero_prod Z W) where
  admissible := b.admissible.zero_product Z
  chartMap := b.zeroProductChart Z
  chartMap_bijective := b.zeroProductChart_bijective Z
  head x i := (congrFun (b.zeroProductChart_coordinates Z x) i.castSucc).trans
    (blowupCoordinates_head _ _ i)
  last x := (congrFun (b.zeroProductChart_coordinates Z x) (Fin.last k)).trans
    (blowupCoordinates_last _ _)
  volume x := by
    obtain ⟨z,w,rfl⟩ := exists_rvPackPair Z.obj.domain W.underlying.obj.domain x
    rw [b.zeroProductChart_pair]
    change (PositiveRVVolumeObject.zero_prod Z W).form.value _ =
      (PositiveRVVolumeObject.zero_prod Z U).form.value (rvPackPair _ _ z (b.projection w))
    rw [zeroPositiveProduct_density,zeroPositiveProduct_density,rvUnpack_pair,rvUnpack_pair]
    exact b.volume w

end IntegrationInACVF.Section7
