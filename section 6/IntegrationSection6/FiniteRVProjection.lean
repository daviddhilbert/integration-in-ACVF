import IntegrationSection6.FiniteRVGeometry

/-! Remark6.2 as a morphism inside RV[k]. The actual definable projection
restricts to the inherited finite-volume full subcategory. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

def elementaryProjection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U : RVFiniteObject (M := M) S k) (i : Fin k) (h : Admissible U i) :
    elementary hκ hs hsmall U i h ⟶ U :=
  ObjectProperty.homMk (IntegrationInACVF.Section6.elementaryProjectionHom hκ hs hsmall U.obj i h)

theorem no_elementary_degree_zero (U V : RVFiniteObject (M := M) S 0) :
    ¬ Nonempty (ElementaryBlowup U V) :=
  no_elementaryBlowup_degree_zero U.obj V.obj

end IntegrationInACVF.Section6.FiniteRV
