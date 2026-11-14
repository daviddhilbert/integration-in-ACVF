import Integration7.ZeroFactorVolumeMaps
import Integration7.ZeroFactorVolumeSwap
import Integration7.RVAlmostEverywhereProducts
import Integration7.VolumeAlmostEverywhere
import Integration7.GammaVolumeCriterion
import Section9.GenericRVJacobian

/-! Only the positive factor contributes a Jacobian. A generic Jacobian
of the actual product is compared with it on their nested correspondences. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def RVVolumeIso.prod_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : RVFiniteObject (M := M) (C.base : Set M) 0}
    (f : RVVolumeIso U V) (g : Z ≅ T) : RVVolumeIso (U.prod_zero Z) (V.prod_zero T) where
  iso := f.zeroProductUnderlying g
  gamma x := by
    apply gammaVolumeEquation_of_absoluteRatio (f.zeroProductUnderlying g) x
    rw [f.zeroProductMap_volumeRatio g,f.zeroProductUnderlying_apply g,
      f.zeroProductMap_coordinates g,zeroProductEssentialChart_coordinates]
    exact f.absolute_volumeRatio _
  rv := by
    have hlocal := f.rv.product_right_bound Z.obj.domain (finiteVolumeDomain_dim_le Z)
    have hsource := RVAlmostEverywhere.pullback_injective (zeroProductEssentialPackChart U Z)
      (zeroProductEssentialPackChart_bijective U Z).1 hlocal
    obtain ⟨ω,D,hD,hd,hω⟩ := exists_definable_generic_RVJacobian hc C (Nat.zero_lt_succ k)
      (f.zeroProductUnderlying g) (U.prod_zero Z).essential_nonzero (V.prod_zero T).essential_nonzero
    have hfull : RVAlmostEverywhere (U.prod_zero Z).essential.obj.domain (k+1) (fun x =>
        IsRVJacobianAt (volumeCorrespondence (finiteIsoMap (f.zeroProductUnderlying g))).carrier
          ((U.prod_zero Z).essential.obj.value x)
          ((V.prod_zero T).essential.obj.value (finiteIsoMap (f.zeroProductUnderlying g) x)) ((ω x).val 0)) :=
      ⟨D,hD,hd,hω⟩
    apply RVAlmostEverywhere.mono (hsource.and hc C hfull)
    rintro x ⟨hfactor,hfull⟩
    simp only [zeroProductEssentialPackChart_unpack] at hfactor
    have hfull0 := hfull
    change IsRVJacobianAt (volumeCorrespondence (f.zeroProductMap g)).carrier
      ((U.prod_zero Z).essential.obj.value x) ((V.prod_zero T).essential.obj.value (f.zeroProductMap g x))
      ((ω x).val 0) at hfull
    rw [zeroProductEssentialChart_coordinates,f.zeroProductMap_coordinates g] at hfull
    have he := rvJacobian_eq_of_subset (f.zeroProductCorrespondence_subset g) hfull hfactor
    have hvalue := he.trans (f.zeroProductMap_volumeRatio g x).symm
    rw [← hvalue]
    exact hfull0

def RVVolumeIso.zero_prod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : RVFiniteObject (M := M) (C.base : Set M) 0}
    (g : Z ≅ T) (f : RVVolumeIso U V) :
    RVVolumeIso (PositiveRVVolumeObject.zero_prod Z U) (PositiveRVVolumeObject.zero_prod T V) :=
  (((volumeZeroProductSwapIso hc C U Z).symm hc C).trans hc C (f.prod_zero hc C g)).trans hc C
    (volumeZeroProductSwapIso hc C V T)

end IntegrationInACVF.Section7
