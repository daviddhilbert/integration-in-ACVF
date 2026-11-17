module

public import Integration7.SignedVolumeProductSwap
public import Integration7.ConstantCoordinateVolumeIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! In smaller RV dimension the unsigned product swap is itself a
volume isomorphism. Its full Gamma equation is still checked pointwise;
only the strictly lower-dimensional RV equation is vacuous. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def unsignedProductSwapObject (U : PositiveRVVolumeObject (M := M) S n)
    (V : PositiveRVVolumeObject (M := M) S m) : PositiveRVVolumeObject (M := M) S ((n+1)+m) :=
  (V.prod U).reindexDegree (positiveProduct_degree_swap n m)

theorem unsigned_product_swap_density
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (w : (U.prod V).underlying.obj.domain) :
    (unsignedProductSwapObject U V).form.value (rvProductSwapMap U.underlying.obj V.underlying.obj w) =
      (U.prod V).form.value w := by
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.underlying.obj.domain V.underlying.obj.domain w
  rw [rvProductSwapMap_pair]
  change (V.prod U).form.value (rvPackPair V.underlying.obj.domain U.underlying.obj.domain v u) = _
  rw [positiveProduct_density_pair,positiveProduct_density_pair,mul_comm]

def volumeUnsignedProductSwapIsoOfDim
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m)
    (hd : rvDim (U.prod V).essential.obj.domain < ((n+1)+m)+1) :
    RVVolumeIso (U.prod V) (unsignedProductSwapObject U V) := by
  let σ := positiveProductSwapPermutation n m
  let eFull : (U.prod V).underlying ≅ (unsignedProductSwapObject U V).underlying :=
    rvFiniteIsoOfAmbient (rvIsoOfLabelEquiv
      (U := (U.prod V).underlying.obj) (V := (unsignedProductSwapObject U V).underlying.obj)
      (rvProductSwapMap U.underlying.obj V.underlying.obj)
      (rvProductSwapMap_bijective U.underlying.obj V.underlying.obj)
      (rvReindexEquiv σ) (rvWeight_reindex σ) (signedProductSwap_coordinates C U V))
  let e := rvFiniteEssentialIso eFull
  apply RVVolumeIso.of_gamma_product_of_lower_dimension e hd
  · intro u
    exact (unsigned_product_swap_density U V ⟨u.val,rvEssentialLabels_subset _ u.property⟩).symm
  · intro u
    let u0 : (U.prod V).underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset _ u.property⟩
    change (∏ i, Values.vrv ((U.prod V).underlying.obj.value u0 i)) =
      ∏ i, Values.vrv ((unsignedProductSwapObject U V).underlying.obj.value
        (rvProductSwapMap U.underlying.obj V.underlying.obj u0) i)
    have hCoord := signedProductSwap_coordinates C U V u0
    change (unsignedProductSwapObject U V).underlying.obj.value
      (rvProductSwapMap U.underlying.obj V.underlying.obj u0) = (U.prod V).underlying.obj.value u0 ∘ σ at hCoord
    rw [hCoord]
    exact (Equiv.prod_comp σ (fun i => Values.vrv ((U.prod V).underlying.obj.value u0 i))).symm

end IntegrationInACVF.Section7
