import Integration7.ElementaryBlowupConstruction
import Integration7.VolumeProductPointwise
import IntegrationSection6.ElementaryRightProduct

/-! Multiplying an elementary volume blowup by a left factor retains
the distinguished last coordinate. The chart and density are actual products. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.prod rvFiniteProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n k : ℕ}

theorem ElementaryBlowup.coordinates {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (w : W.underlying.obj.domain) :
    W.underlying.obj.value w =
      blowupCoordinates (U.underlying.obj.value (b.projection w)) ((b.parameter w).val 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (b.last w).trans (blowupCoordinates_last _ _).symm
  · exact (b.head w j).trans (blowupCoordinates_head _ _ j).symm

theorem BlowupAdmissible.product_left {U : PositiveRVVolumeObject (M := M) S k}
    (h : BlowupAdmissible U) (R : PositiveRVVolumeObject (M := M) S n) :
    BlowupAdmissible (R.prod U) := by
  have hlast : Fin.natAdd (n+1) (Fin.last k) = Fin.last ((n+1)+k) := Fin.ext rfl
  constructor
  · intro x
    obtain ⟨r,u,rfl⟩ := exists_rvPackPair R.underlying.obj.domain U.underlying.obj.domain x
    rw [positiveProduct_coordinates_pair,← hlast]
    simpa only [rvAppend,Fin.append_right] using h.nonzero u
  · intro x
    obtain ⟨r,u,rfl⟩ := exists_rvPackPair R.underlying.obj.domain U.underlying.obj.domain x
    rw [positiveProduct_coordinates_pair,← hlast]
    simp only [rvAppend,Fin.append_right]
    change AlgebraicAt (Section6.coordinateBase S (Fin.natAdd (n+1) (Fin.last k))
      (rvAppend (R.underlying.obj.value r) (U.underlying.obj.value u))) .rv
      (U.underlying.obj.value u (Fin.last k)).val
    apply (h.algebraic u).mono
    rintro z (hz | ⟨i,hi,he⟩)
    · exact Or.inl hz
    · refine Or.inr ⟨Fin.natAdd (n+1) i,?_,?_⟩
      · intro heq
        exact hi (Fin.natAdd_injective (k+1) (n+1) heq)
      · simpa only [rvAppend,Fin.append_right] using he

def ElementaryBlowup.productChart {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (R : PositiveRVVolumeObject (M := M) S n) :
    Map (R.prod W).underlying.obj.domain
      ((R.prod U).underlying.obj.domain.prod (blowupConeSet S)) :=
  ((Map.prodMap (rvPack R.underlying.obj.domain U.underlying.obj.domain).toImage
    (Map.id (blowupConeSet S))).comp
      ((Map.prodAssoc R.underlying.obj.domain U.underlying.obj.domain (blowupConeSet S)).inverse
        (Map.prodAssoc_bijective _ _ _))).comp
    ((Map.prodMap (Map.id R.underlying.obj.domain) b.chartMap).comp
      (rvUnpack R.underlying.obj.domain W.underlying.obj.domain))

theorem ElementaryBlowup.productChart_bijective {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (R : PositiveRVVolumeObject (M := M) S n) :
    Function.Bijective (b.productChart R) :=
  ((Map.prodMap_bijective _ _ (rvPackToImage_bijective _ _) Function.bijective_id).comp
    (Section6.mapInverse_bijective _ (Map.prodAssoc_bijective _ _ _))).comp
    ((Map.prodMap_bijective _ _ Function.bijective_id b.chartMap_bijective).comp
      (rvUnpack_bijective _ _))

theorem ElementaryBlowup.productChart_pair {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (R : PositiveRVVolumeObject (M := M) S n)
    (r : R.underlying.obj.domain) (w : W.underlying.obj.domain) :
    b.productChart R (rvPackPair R.underlying.obj.domain W.underlying.obj.domain r w) =
      ⟨((rvPackPair R.underlying.obj.domain U.underlying.obj.domain r (b.projection w)).val,
        (b.parameter w).val),
        (rvPackPair R.underlying.obj.domain U.underlying.obj.domain r (b.projection w)).property,
        (b.parameter w).property⟩ := by
  have h := Map.inverse_apply
    (Map.prodAssoc R.underlying.obj.domain U.underlying.obj.domain (blowupConeSet S))
    (Map.prodAssoc_bijective _ _ _)
    ⟨((r.val,(b.projection w).val),(b.parameter w).val),
      ⟨r.property,(b.projection w).property⟩,(b.parameter w).property⟩
  simp only [ElementaryBlowup.productChart,Map.comp_apply,rvUnpack_pair]
  change (Map.prodMap (rvPack R.underlying.obj.domain U.underlying.obj.domain).toImage
    (Map.id (blowupConeSet S)))
    ((Map.prodAssoc R.underlying.obj.domain U.underlying.obj.domain (blowupConeSet S)).inverse
      (Map.prodAssoc_bijective _ _ _)
      (Map.prodAssoc R.underlying.obj.domain U.underlying.obj.domain (blowupConeSet S)
        ⟨((r.val,(b.projection w).val),(b.parameter w).val),
          ⟨r.property,(b.projection w).property⟩,(b.parameter w).property⟩)) = _
  rw [h]
  rfl

theorem ElementaryBlowup.productChart_coordinates {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (R : PositiveRVVolumeObject (M := M) S n)
    (x : (R.prod W).underlying.obj.domain) :
    (R.prod W).underlying.obj.value x = blowupCoordinates
      ((R.prod U).underlying.obj.value (Map.prodFst _ _ (b.productChart R x)))
      ((b.productChart R x).val.2 0) := by
  obtain ⟨r,w,rfl⟩ := exists_rvPackPair R.underlying.obj.domain W.underlying.obj.domain x
  rw [b.productChart_pair]
  change (R.prod W).underlying.obj.value _ = blowupCoordinates
    ((R.prod U).underlying.obj.value (rvPackPair _ _ r (b.projection w))) _
  rw [positiveProduct_coordinates_pair,positiveProduct_coordinates_pair,b.coordinates]
  have hlast : Fin.natAdd (n+1) (Fin.last k) = Fin.last ((n+1)+k) := Fin.ext rfl
  exact (Section6.blowupValue_append_right (Fin.last k) _ _ _).symm.trans
    (congrArg (fun i => Section6.blowupValue i _ _) hlast)

def ElementaryBlowup.product_left {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) (R : PositiveRVVolumeObject (M := M) S n) :
    ElementaryBlowup (R.prod U) (R.prod W) where
  admissible := b.admissible.product_left R
  chartMap := b.productChart R
  chartMap_bijective := b.productChart_bijective R
  head x i := (congrFun (b.productChart_coordinates R x) i.castSucc).trans
    (blowupCoordinates_head _ _ i)
  last x := (congrFun (b.productChart_coordinates R x) (Fin.last ((n+1)+k))).trans
    (blowupCoordinates_last _ _)
  volume x := by
    obtain ⟨r,w,rfl⟩ := exists_rvPackPair R.underlying.obj.domain W.underlying.obj.domain x
    rw [b.productChart_pair]
    change (R.prod W).form.value _ =
      (R.prod U).form.value (rvPackPair _ _ r (b.projection w))
    rw [positiveProduct_density_pair,positiveProduct_density_pair,b.volume]
    rfl

end IntegrationInACVF.Section7
