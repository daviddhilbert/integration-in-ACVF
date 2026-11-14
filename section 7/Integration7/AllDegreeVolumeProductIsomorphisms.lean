import Integration7.ZeroFactorProductBridges
import Integration7.RVVolumeProducts
import Section4.RVProductMorphisms

/-! One product-isomorphism operation for every pair of actual volume
degrees. Degree zero retains ordinary RV isomorphisms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeProductIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} {U U' : RVVolumeObject (M := M) (C.base : Set M) n}
    {V V' : RVVolumeObject (M := M) (C.base : Set M) m}
    (f : RVVolumeIsoInDegree (C.base : Set M) n U U')
    (g : RVVolumeIsoInDegree (C.base : Set M) m V V') :
    RVVolumeIsoInDegree (C.base : Set M) (n+m)
      (rvVolumeProduct (C.base : Set M) n m U V) (rvVolumeProduct (C.base : Set M) n m U' V') := by
  cases n with
  | zero =>
    cases m with
    | zero =>
      exact rvFiniteIsoOfAmbient (rvProductIso
        ((finiteVolumeProperty (C.base : Set M) 0).ι.mapIso f)
        ((finiteVolumeProperty (C.base : Set M) 0).ι.mapIso g))
    | succ m =>
      exact ((volumeProductZeroPositiveIso hc C U V).trans hc C
        ((RVVolumeIso.zero_prod hc C f g).reindexDegree hc C (Nat.zero_add m))).trans hc C
          ((volumeProductZeroPositiveIso hc C U' V').symm hc C)
  | succ n =>
    cases m with
    | zero =>
      exact ((volumeProductPositiveZeroIso hc C U V).trans hc C (f.prod_zero hc C g)).trans hc C
        ((volumeProductPositiveZeroIso hc C U' V').symm hc C)
    | succ m => exact f.prod hc C g

end IntegrationInACVF.Section7
