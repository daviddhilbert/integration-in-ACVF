import Integration7.ZeroFactorVolumeObjects
import Integration7.NondegenerateFiniteIso

/-! Essential charts for a positive object times an ordinary RV[0]
object. Only the positive factor has essential coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.prod_zero rvFiniteProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def zeroProductEssentialChart (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) :
    Map (U.prod_zero Z).essential.obj.domain (U.essential.obj.domain.prod Z.obj.domain) := by
  let F := (rvUnpack U.underlying.obj.domain Z.obj.domain).comp
    (Map.inclusion (rvEssentialLabels_subset (U.prod_zero Z).underlying.obj))
  refine F.corestrict ?_
  intro x
  refine ⟨?_,(F x).property.2⟩
  apply (mem_rvEssentialLabels U.underlying.obj (Map.prodFst _ _ (F x))).mpr
  intro i hz
  have he := positiveZeroProduct_coordinates U Z
    ⟨x.val,rvEssentialLabels_subset (U.prod_zero Z).underlying.obj x.property⟩
  exact (U.prod_zero Z).essential_nonzero x i ((congrArg (fun t => (t i).val) he).trans hz)

def zeroProductEssentialInverseChart (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) :
    Map (U.essential.obj.domain.prod Z.obj.domain) (U.prod_zero Z).essential.obj.domain := by
  let I := Map.prodMap (Map.inclusion (rvEssentialLabels_subset U.underlying.obj)) (Map.id Z.obj.domain)
  let G := (rvPack U.underlying.obj.domain Z.obj.domain).toImage.comp I
  refine G.corestrict ?_
  intro p
  apply (mem_rvEssentialLabels (U.prod_zero Z).underlying.obj (G p)).mpr
  have h := positiveZeroProduct_coordinates U Z (G p)
  have he : rvUnpack U.underlying.obj.domain Z.obj.domain (G p) = I p := rvUnpack_pack _ _ _
  have hc : (U.prod_zero Z).underlying.obj.value (G p) =
      U.essential.obj.value (Map.prodFst _ _ p) :=
    h.trans (congrArg (fun q => U.underlying.obj.value (Map.prodFst _ _ q)) he)
  intro i
  exact fun hz => U.essential_nonzero (Map.prodFst _ _ p) i
    ((congrArg (fun t => (t i).val) hc).symm.trans hz)

theorem zeroProductEssentialChart_inverse (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) (p : U.essential.obj.domain.prod Z.obj.domain) :
    zeroProductEssentialChart U Z (zeroProductEssentialInverseChart U Z p) = p := by
  apply Subtype.ext
  change (rvUnpack U.underlying.obj.domain Z.obj.domain
    ((rvPack U.underlying.obj.domain Z.obj.domain).toImage
      ⟨p.val,rvEssentialLabels_subset U.underlying.obj p.property.1,p.property.2⟩)).val = p.val
  exact congrArg (fun q : U.underlying.obj.domain.prod Z.obj.domain => q.val) (rvUnpack_pack _ _ _)

theorem zeroProductEssentialInverseChart_chart (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) (x : (U.prod_zero Z).essential.obj.domain) :
    zeroProductEssentialInverseChart U Z (zeroProductEssentialChart U Z x) = x := by
  apply Subtype.ext
  change ((rvPack U.underlying.obj.domain Z.obj.domain).toImage
    (rvUnpack U.underlying.obj.domain Z.obj.domain
      ⟨x.val,rvEssentialLabels_subset (U.prod_zero Z).underlying.obj x.property⟩)).val = x.val
  exact congrArg (fun q : (U.prod_zero Z).underlying.obj.domain => q.val) (rvPack_unpack _ _ _)

theorem zeroProductEssentialChart_bijective (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) : Function.Bijective (zeroProductEssentialChart U Z) :=
  ⟨Function.LeftInverse.injective (zeroProductEssentialInverseChart_chart U Z),
    Function.RightInverse.surjective (zeroProductEssentialChart_inverse U Z)⟩

theorem zeroProductEssentialChart_coordinates (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) (x : (U.prod_zero Z).essential.obj.domain) :
    (U.prod_zero Z).essential.obj.value x =
      U.essential.obj.value (Map.prodFst _ _ (zeroProductEssentialChart U Z x)) :=
  positiveZeroProduct_coordinates U Z ⟨x.val,rvEssentialLabels_subset (U.prod_zero Z).underlying.obj x.property⟩

theorem zeroProductEssentialChart_density (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) (x : (U.prod_zero Z).essential.obj.domain) :
    (U.prod_zero Z).essentialForm.value x =
      U.essentialForm.value (Map.prodFst _ _ (zeroProductEssentialChart U Z x)) := rfl

def zeroProductEssentialPackChart (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) :
    Map (U.prod_zero Z).essential.obj.domain (rvProductDomain U.essential.obj.domain Z.obj.domain) :=
  (rvPack U.essential.obj.domain Z.obj.domain).toImage.comp (zeroProductEssentialChart U Z)

theorem zeroProductEssentialPackChart_bijective (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) : Function.Bijective (zeroProductEssentialPackChart U Z) :=
  (rvPackToImage_bijective _ _).comp (zeroProductEssentialChart_bijective U Z)

theorem zeroProductEssentialPackChart_unpack (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) (x : (U.prod_zero Z).essential.obj.domain) :
    rvUnpack U.essential.obj.domain Z.obj.domain (zeroProductEssentialPackChart U Z x) =
      zeroProductEssentialChart U Z x := rvUnpack_pack _ _ _

end IntegrationInACVF.Section7
