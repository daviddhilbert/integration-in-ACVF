import Integration7.HKZeroRVVolumeIsomorphisms
import Integration7.HKVolumeFormTransport
import Integration7.ZeroFactorVolumeObjects

/-! Actual products for the corrected all-degree objects. Densities from
both factors survive, including products of two zero-degree objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def product (S : Set M) (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m) :
    RVVolumeObject (M := M) S (n+m) :=
  ofForm S (n+m) (rvFiniteProductObject (underlying S n U) (underlying S m V))
    (((form S n U).prod (form S m V)).pullback
      (rvUnpack (underlying S n U).obj.domain (underlying S m V).obj.domain))

@[simp] theorem product_underlying (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m) :
    underlying S (n+m) (product S n m U V) =
      rvFiniteProductObject (underlying S n U) (underlying S m V) := ofForm_underlying _ _ _

theorem product_density (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m)
    (a : (rvFiniteProductObject (underlying S n U) (underlying S m V)).obj.domain) :
    (form S (n+m) (product S n m U V)).value ((product_underlying n m U V).symm ▸ a) =
      (form S n U).value (Map.prodFst _ _ (rvUnpack _ _ a)) *
      (form S m V).value (Map.prodSnd _ _ (rvUnpack _ _ a)) := ofForm_density _ _ _ _

def zeroProductMultiplier (Z : ZeroRVVolumeObject (M := M) S)
    (U : PositiveRVVolumeObject (M := M) S k) :
    VolumeForm (PositiveRVVolumeObject.zero_prod Z.underlying U).underlying.obj.domain :=
  Z.form.pullback ((Map.prodFst _ _).comp (rvUnpack Z.underlying.obj.domain U.underlying.obj.domain))

def zeroProduct (Z : ZeroRVVolumeObject (M := M) S)
    (U : PositiveRVVolumeObject (M := M) S k) : PositiveRVVolumeObject (M := M) S k :=
  multiplyForm (PositiveRVVolumeObject.zero_prod Z.underlying U) (zeroProductMultiplier Z U)

@[simp] theorem zeroProduct_density (Z : ZeroRVVolumeObject (M := M) S)
    (U : PositiveRVVolumeObject (M := M) S k) (a : (zeroProduct Z U).underlying.obj.domain) :
    (zeroProduct Z U).form.value a =
      Z.form.value (Map.prodFst _ _ (rvUnpack _ _ a)) *
      U.form.value (Map.prodSnd _ _ (rvUnpack _ _ a)) := rfl

theorem zeroProduct_coordinates (Z : ZeroRVVolumeObject (M := M) S)
    (U : PositiveRVVolumeObject (M := M) S k) (a : (zeroProduct Z U).underlying.obj.domain) :
    (zeroProduct Z U).underlying.obj.value a =
      U.underlying.obj.value (Map.prodSnd _ _ (rvUnpack _ _ a)) :=
  zeroPositiveProduct_coordinates Z.underlying U a

def positiveZeroMultiplier (U : PositiveRVVolumeObject (M := M) S k)
    (Z : ZeroRVVolumeObject (M := M) S) : VolumeForm (U.prod_zero Z.underlying).underlying.obj.domain :=
  Z.form.pullback ((Map.prodSnd _ _).comp (rvUnpack U.underlying.obj.domain Z.underlying.obj.domain))

def positiveZeroProduct (U : PositiveRVVolumeObject (M := M) S k)
    (Z : ZeroRVVolumeObject (M := M) S) : PositiveRVVolumeObject (M := M) S k :=
  multiplyForm (U.prod_zero Z.underlying) (positiveZeroMultiplier U Z)

@[simp] theorem positiveZeroProduct_density (U : PositiveRVVolumeObject (M := M) S k)
    (Z : ZeroRVVolumeObject (M := M) S) (a : (positiveZeroProduct U Z).underlying.obj.domain) :
    (positiveZeroProduct U Z).form.value a =
      U.form.value (Map.prodFst _ _ (rvUnpack _ _ a)) *
      Z.form.value (Map.prodSnd _ _ (rvUnpack _ _ a)) := mul_comm _ _

theorem positiveZeroProduct_coordinates (U : PositiveRVVolumeObject (M := M) S k)
    (Z : ZeroRVVolumeObject (M := M) S) (a : (positiveZeroProduct U Z).underlying.obj.domain) :
    (positiveZeroProduct U Z).underlying.obj.value a =
      U.underlying.obj.value (Map.prodFst _ _ (rvUnpack _ _ a)) :=
  IntegrationInACVF.Section7.positiveZeroProduct_coordinates U Z.underlying a

end IntegrationInACVF.Section7.HK
