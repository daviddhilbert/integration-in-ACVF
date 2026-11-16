module

public import Integration7.HKRVVolumeProducts
public import Integration7.ZeroFactorVolumeIsomorphisms

@[expose] public section

/-! The weighted zero scalar action respects actual volume isomorphisms.
The existing product charts are reused; the varying scalar weights agree
on corresponding labels and therefore cancel in the volume ratio. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

set_option allowUnsafeReducibility true in
attribute [local reducible] zeroProduct positiveZeroProduct multiplyForm
  PositiveRVVolumeObject.zero_prod PositiveRVVolumeObject.prod_zero rvFiniteProductObject

def positiveZeroProductIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    (f : RVVolumeIso U V) (g : ZeroRVVolumeIso Z T) :
    RVVolumeIso (positiveZeroProduct U Z) (positiveZeroProduct V T) := by
  apply multiplyFormIso (f.prod_zero hc C g.iso)
    (positiveZeroMultiplier U Z) (positiveZeroMultiplier V T)
  intro u
  change Z.form.value (Map.prodSnd _ _ (zeroProductEssentialChart U Z.underlying u)) =
    T.form.value (Map.prodSnd _ _ (zeroProductEssentialChart V T.underlying (f.zeroProductMap g.iso u)))
  rw [f.zeroProductMap_chart g.iso]
  exact g.density _

def mixedProductSwapIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    RVVolumeIso (positiveZeroProduct U Z) (zeroProduct Z U) := by
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := (positiveZeroProduct U Z).underlying.obj) (V := (zeroProduct Z U).underlying.obj)
    (rvProductSwapMap U.underlying.obj Z.underlying.obj)
    (rvProductSwapMap_bijective U.underlying.obj Z.underlying.obj)
    (volumeZeroProductSwap_coordinates U Z.underlying))
  apply RVVolumeIso.of_preserving_coordinates_full hc C e
    (volumeZeroProductSwap_coordinates U Z.underlying)
  intro x
  change (zeroProduct Z U).form.value (rvProductSwapMap U.underlying.obj Z.underlying.obj x) =
    (positiveZeroProduct U Z).form.value x
  obtain ⟨u,z,rfl⟩ := exists_rvPackPair U.underlying.obj.domain Z.underlying.obj.domain x
  rw [rvProductSwapMap_pair, zeroProduct_density, positiveZeroProduct_density, rvUnpack_pair, rvUnpack_pair]
  exact mul_comm _ _

def zeroProductIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    (g : ZeroRVVolumeIso Z T) (f : RVVolumeIso U V) : RVVolumeIso (zeroProduct Z U) (zeroProduct T V) :=
  (((mixedProductSwapIso hc C U Z).symm hc C).trans hc C
    (positiveZeroProductIso hc C f g)).trans hc C (mixedProductSwapIso hc C V T)

end IntegrationInACVF.Section7.HK
