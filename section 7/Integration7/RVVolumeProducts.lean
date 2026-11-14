import Integration7.VolumeProductMaps
import Integration7.RVProductJacobianComparison
import Integration7.RVAlmostEverywhereProducts
import Integration7.GammaVolumeCriterion
import Section9.GenericRVJacobian

/-! Genuine products of positive RV volume isomorphisms. The full
and factor Jacobians are obtained generically and compared through
their complementary tangent projections. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem absoluteWeight_append {p q : ℕ}
    (t : Fin p → CanonicalRV.RVSort M) (s : Fin q → CanonicalRV.RVSort M) :
    (∏ i, RVOperations.absoluteHom (Fin.append t s i)) =
      (∏ i, RVOperations.absoluteHom (t i)) * ∏ i, RVOperations.absoluteHom (s i) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

def RVVolumeIso.prod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' : PositiveRVVolumeObject (M := M) (C.base : Set M) n}
    {V V' : PositiveRVVolumeObject (M := M) (C.base : Set M) m}
    (f : RVVolumeIso U U') (g : RVVolumeIso V V') : RVVolumeIso (U.prod V) (U'.prod V') where
  iso := f.productUnderlying g
  gamma w := by
    apply gammaVolumeEquation_of_absoluteRatio (f.productUnderlying g) w
    let u := Map.prodFst U.essential.obj.domain V.essential.obj.domain (productEssentialChart U V w)
    let v := Map.prodSnd U.essential.obj.domain V.essential.obj.domain (productEssentialChart U V w)
    have hpair := congrArg₂ (fun x y => x * y) (f.absolute_volumeRatio u) (g.absolute_volumeRatio v)
    simp only [volumeRatio, map_div₀] at hpair
    change RVOperations.absoluteHom ((U.prod V).essentialForm.value w /
      (U'.prod V').essentialForm.value (f.productMap g w)) =
        (∏ i, RVOperations.absoluteHom ((U'.prod V').essential.obj.value (f.productMap g w) i)) /
          ∏ i, RVOperations.absoluteHom ((U.prod V).essential.obj.value w i)
    rw [f.productMap_density g, productEssentialChart_density,
      f.productMap_coordinates g, productEssentialChart_coordinates]
    simp only [map_div₀, map_mul]
    simp only [div_mul_div_comm] at hpair
    exact hpair.trans (congrArg₂ (fun x y => x / y)
      (absoluteWeight_append (U'.essential.obj.value (finiteIsoMap f.iso u))
        (V'.essential.obj.value (finiteIsoMap g.iso v))).symm
      (absoluteWeight_append (U.essential.obj.value u) (V.essential.obj.value v)).symm)
  rv := by
    have hparts := RVAlmostEverywhere.product hc C
      (finiteVolumeDomain_dim_le U.essential) (finiteVolumeDomain_dim_le V.essential) f.rv g.rv
    have hsource := RVAlmostEverywhere.pullback_injective (productEssentialPackChart U V)
      (productEssentialPackChart_bijective U V).1 hparts
    obtain ⟨ω, D, hD, hd, hω⟩ := exists_definable_generic_RVJacobian hc C
      (Nat.zero_lt_succ ((n + 1) + m)) (f.productUnderlying g)
      (U.prod V).essential_nonzero (U'.prod V').essential_nonzero
    have hfull : RVAlmostEverywhere (U.prod V).essential.obj.domain (((n + 1) + m) + 1)
        (fun w => IsRVJacobianAt (volumeCorrespondence (finiteIsoMap (f.productUnderlying g))).carrier
          ((U.prod V).essential.obj.value w)
          ((U'.prod V').essential.obj.value (finiteIsoMap (f.productUnderlying g) w)) ((ω w).val 0)) :=
      ⟨D, hD, hd, hω⟩
    apply RVAlmostEverywhere.mono (hsource.and hc C hfull)
    rintro w ⟨hparts, hfull⟩
    simp only [productEssentialPackChart_unpack] at hparts
    obtain ⟨hF, hG⟩ := hparts
    have hfull0 := hfull
    change IsRVJacobianAt (volumeCorrespondence (f.productMap g)).carrier
      ((U.prod V).essential.obj.value w) ((U'.prod V').essential.obj.value (f.productMap g w))
      ((ω w).val 0) at hfull
    rw [f.productMap_coordinates g, productEssentialChart_coordinates] at hfull
    have he := rvJacobian_eq_product_of_projections (n := n + 1) (m := m + 1) (f.productCorrespondence_left g)
      (f.productCorrespondence_right g) _ _ _ _ hfull hF hG
    have hvalue := he.trans (f.productMap_volumeRatio g w).symm
    rw [← hvalue]
    exact hfull0

end IntegrationInACVF.Section7
