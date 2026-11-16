module

public import Integration7.HKRVProductBridges
public import Integration7.RVVolumeProducts
public import Section4.RVProductMorphisms

@[expose] public section

/-! Products respect measured isomorphisms in every pair of degrees.
The zero-zero case preserves both weights exactly, and the mixed cases
use the corrected scalar charts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def zeroZeroProductIso {U U' V V' : ZeroRVVolumeObject (M := M) S}
    (f : ZeroRVVolumeIso U U') (g : ZeroRVVolumeIso V V') :
    ZeroRVVolumeIso (product S 0 0 U V) (product S 0 0 U' V') where
  iso := rvFiniteIsoOfAmbient (rvProductIso
    ((finiteVolumeProperty S 0).ι.mapIso f.iso) ((finiteVolumeProperty S 0).ι.mapIso g.iso))
  density a := by
    change U.form.value (Map.prodFst _ _ (rvUnpack _ _ a)) *
      V.form.value (Map.prodSnd _ _ (rvUnpack _ _ a)) =
      U'.form.value (Map.prodFst _ _ (rvUnpack _ _
        (rvProductMap (finiteIsoMap f.iso) (finiteIsoMap g.iso) a))) *
      V'.form.value (Map.prodSnd _ _ (rvUnpack _ _
        (rvProductMap (finiteIsoMap f.iso) (finiteIsoMap g.iso) a)))
    rw [rvProductMap_unpack]
    exact congrArg₂ (fun x y => x*y) (f.density _) (g.density _)

def productIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} {U U' : RVVolumeObject (M := M) (C.base : Set M) n}
    {V V' : RVVolumeObject (M := M) (C.base : Set M) m}
    (f : rvVolumeIsoInDegree (C.base : Set M) n U U')
    (g : rvVolumeIsoInDegree (C.base : Set M) m V V') :
    rvVolumeIsoInDegree (C.base : Set M) (n+m)
      (product (C.base : Set M) n m U V) (product (C.base : Set M) n m U' V') := by
  cases n with
  | zero =>
    cases m with
    | zero => exact zeroZeroProductIso f g
    | succ m =>
      exact ((productZeroPositiveIso hc C U V).trans hc C
        ((zeroProductIso hc C f g).reindexDegree hc C (Nat.zero_add m))).trans hc C
          ((productZeroPositiveIso hc C U' V').symm hc C)
  | succ n =>
    cases m with
    | zero =>
      exact ((productPositiveZeroIso hc C U V).trans hc C (positiveZeroProductIso hc C f g)).trans hc C
        ((productPositiveZeroIso hc C U' V').symm hc C)
    | succ m => exact f.prod hc C g

end IntegrationInACVF.Section7.HK
