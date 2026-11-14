import Integration7.GradedVolumeProducts
import Integration7.NondegenerateFiniteIso
import Section4.RVProductMorphisms

/-! Actual essential product charts. A product label is essential
exactly when both of its factor labels are essential. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def productEssentialChart
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m) :
    Map (U.prod V).essential.obj.domain (U.essential.obj.domain.prod V.essential.obj.domain) := by
  let F := (rvUnpack U.underlying.obj.domain V.underlying.obj.domain).comp
    (Map.inclusion (rvEssentialLabels_subset (U.prod V).underlying.obj))
  refine F.corestrict ?_
  intro w
  let u := Map.prodFst U.underlying.obj.domain V.underlying.obj.domain (F w)
  let v := Map.prodSnd U.underlying.obj.domain V.underlying.obj.domain (F w)
  constructor
  · apply (mem_rvEssentialLabels U.underlying.obj u).mpr
    intro i
    have h := (U.prod V).essential_nonzero w (Fin.castAdd (m + 1) i)
    change ((Fin.append (U.underlying.obj.value u) (V.underlying.obj.value v))
      (Fin.castAdd (m + 1) i)).val ≠ iRVZero at h
    simpa only [Fin.append_left] using h
  · apply (mem_rvEssentialLabels V.underlying.obj v).mpr
    intro i
    have h := (U.prod V).essential_nonzero w (Fin.natAdd (n + 1) i)
    change ((Fin.append (U.underlying.obj.value u) (V.underlying.obj.value v))
      (Fin.natAdd (n + 1) i)).val ≠ iRVZero at h
    simpa only [Fin.append_right] using h

def productEssentialInverseChart
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m) :
    Map (U.essential.obj.domain.prod V.essential.obj.domain) (U.prod V).essential.obj.domain := by
  let I := Map.prodMap (Map.inclusion (rvEssentialLabels_subset U.underlying.obj))
    (Map.inclusion (rvEssentialLabels_subset V.underlying.obj))
  let G := (rvPack U.underlying.obj.domain V.underlying.obj.domain).toImage.comp I
  refine G.corestrict ?_
  intro p
  apply (mem_rvEssentialLabels (U.prod V).underlying.obj (G p)).mpr
  let u := Map.prodFst U.essential.obj.domain V.essential.obj.domain p
  let v := Map.prodSnd U.essential.obj.domain V.essential.obj.domain p
  have hcoord : (U.prod V).underlying.obj.value (G p) =
      Fin.append (U.essential.obj.value u) (V.essential.obj.value v) := by
    change (rvProductObject U.underlying.obj V.underlying.obj).value
      ((rvPack U.underlying.obj.domain V.underlying.obj.domain).toImage (I p)) = _
    rw [rvProductObject_value, rvUnpack_pack]
    rfl
  intro i
  rw [hcoord]
  refine Fin.addCases (m := n + 1) (n := m + 1) (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using U.essential_nonzero u j
  · simpa only [Fin.append_right] using V.essential_nonzero v j

theorem productEssentialChart_inverse
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (p : U.essential.obj.domain.prod V.essential.obj.domain) :
    productEssentialChart U V (productEssentialInverseChart U V p) = p := by
  apply Subtype.ext
  change (rvUnpack U.underlying.obj.domain V.underlying.obj.domain
    ((rvPack U.underlying.obj.domain V.underlying.obj.domain).toImage
      ⟨p.val, rvEssentialLabels_subset U.underlying.obj p.property.1,
        rvEssentialLabels_subset V.underlying.obj p.property.2⟩)).val = p.val
  exact congrArg (fun q : U.underlying.obj.domain.prod V.underlying.obj.domain => q.val)
    (rvUnpack_pack _ _ _)

theorem productEssentialInverseChart_chart
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (w : (U.prod V).essential.obj.domain) :
    productEssentialInverseChart U V (productEssentialChart U V w) = w := by
  apply Subtype.ext
  change ((rvPack U.underlying.obj.domain V.underlying.obj.domain).toImage
    (rvUnpack U.underlying.obj.domain V.underlying.obj.domain
      ⟨w.val, rvEssentialLabels_subset (U.prod V).underlying.obj w.property⟩)).val = w.val
  exact congrArg (fun q : (U.prod V).underlying.obj.domain => q.val) (rvPack_unpack _ _ _)

theorem productEssentialChart_bijective
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m) :
    Function.Bijective (productEssentialChart U V) :=
  ⟨Function.LeftInverse.injective (productEssentialInverseChart_chart U V),
    Function.RightInverse.surjective (productEssentialChart_inverse U V)⟩

theorem productEssentialChart_coordinates
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (w : (U.prod V).essential.obj.domain) :
    (U.prod V).essential.obj.value w = Fin.append
      (U.essential.obj.value (Map.prodFst _ _ (productEssentialChart U V w)))
      (V.essential.obj.value (Map.prodSnd _ _ (productEssentialChart U V w))) := rfl

theorem productEssentialChart_density
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (w : (U.prod V).essential.obj.domain) :
    (U.prod V).essentialForm.value w =
      U.essentialForm.value (Map.prodFst _ _ (productEssentialChart U V w)) *
      V.essentialForm.value (Map.prodSnd _ _ (productEssentialChart U V w)) := rfl

def productEssentialPackChart
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m) :
    Map (U.prod V).essential.obj.domain (rvProductDomain U.essential.obj.domain V.essential.obj.domain) :=
  (rvPack U.essential.obj.domain V.essential.obj.domain).toImage.comp (productEssentialChart U V)

theorem productEssentialPackChart_bijective
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m) :
    Function.Bijective (productEssentialPackChart U V) :=
  (rvPackToImage_bijective _ _).comp (productEssentialChart_bijective U V)

theorem productEssentialPackChart_unpack
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (w : (U.prod V).essential.obj.domain) :
    rvUnpack U.essential.obj.domain V.essential.obj.domain (productEssentialPackChart U V w) =
      productEssentialChart U V w := rvUnpack_pack _ _ _

end IntegrationInACVF.Section7
