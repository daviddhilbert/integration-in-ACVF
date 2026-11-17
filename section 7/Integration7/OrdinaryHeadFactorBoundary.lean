module

public import Integration7.BasicVolumeRelationObjects
public import Integration7.VolumeDensityRescaling
public import Integration7.EssentialGammaWeight
public import Integration7.ZeroFactorVolumeObjects

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The ordinary RV[0] convention discards all density data. A degree-one
point with a nonunit absolute density therefore cannot be factored as an
ordinary degree-zero object times the unit-density degree-one point.
This checks the boundary of the paper's proposed head factorization;
it is not a disproof of the full principal-ideal theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem ordinary_zero_point_product_weight
    (Z : RVFiniteObject (M := M) S 0)
    (u : (PositiveRVVolumeObject.zero_prod Z (degreeOnePointVolumeObject S)).essential.obj.domain) :
    essentialGammaWeight (PositiveRVVolumeObject.zero_prod Z (degreeOnePointVolumeObject S)) u = 1 := by
  let V := PositiveRVVolumeObject.zero_prod Z (degreeOnePointVolumeObject S)
  let u0 : V.underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset V.underlying.obj u.property⟩
  change RVOperations.absoluteHom (V.form.value u0) *
    (∏ i, RVOperations.absoluteHom (V.underlying.obj.value u0 i)) = 1
  rw [zeroPositiveProduct_density,zeroPositiveProduct_coordinates,degree_one_point_volume_coordinates]
  change RVOperations.absoluteHom (1 : CanonicalRV.RVSort M) *
    (∏ _ : Fin 1, RVOperations.absoluteHom (1 : CanonicalRV.RVSort M)) = 1
  simp only [map_one,Finset.prod_const_one,mul_one]

theorem nonunit_density_point_has_no_ordinary_head_factor
    (c : CanonicalRV.RVSort M) (hS : c.val ∈ S) (h0 : c ≠ 0)
    (hAbs : RVOperations.absoluteHom c ≠ 1) :
    ¬ ∃ Z : RVFiniteObject (M := M) S 0,
      Nonempty (RVVolumeIso ((degreeOnePointVolumeObject S).rescale c hS h0)
        (PositiveRVVolumeObject.zero_prod Z (degreeOnePointVolumeObject S))) := by
  rintro ⟨Z,⟨e⟩⟩
  let U := (degreeOnePointVolumeObject S).rescale c hS h0
  let u0 : U.underlying.obj.domain := ⟨Fin.elim0,Set.mem_univ _⟩
  have hu : u0.val ∈ (rvEssentialLabels U.underlying.obj).carrier := by
    apply (mem_rvEssentialLabels U.underlying.obj u0).mpr
    intro i
    exact (rv_nonzero_iff_raw _).mp one_ne_zero
  let u : U.essential.obj.domain := ⟨u0.val,hu⟩
  have hU : essentialGammaWeight U u = RVOperations.absoluteHom c := by
    change RVOperations.absoluteHom (c * 1) *
      (∏ _ : Fin 1, RVOperations.absoluteHom (1 : CanonicalRV.RVSort M)) = RVOperations.absoluteHom c
    simp only [mul_one,Fin.prod_univ_one,map_one]
  exact hAbs (hU.symm.trans ((e.essentialGammaWeight u).trans
    (ordinary_zero_point_product_weight Z (finiteIsoMap e.iso u))))

theorem admissible_nonunit_point_has_no_ordinary_head_factor
    (hc : CanonicalStructure.IsCanonical (M := M)) (c : CanonicalRV.RVSort M)
    (hS : c.val ∈ S) (h0 : c ≠ 0) (hAbs : RVOperations.absoluteHom c ≠ 1) :
    BlowupAdmissible ((degreeOnePointVolumeObject S).rescale c hS h0) ∧
      ¬ ∃ Z : RVFiniteObject (M := M) S 0,
        Nonempty (RVVolumeIso ((degreeOnePointVolumeObject S).rescale c hS h0)
          (PositiveRVVolumeObject.zero_prod Z (degreeOnePointVolumeObject S))) :=
  ⟨⟨(degreeOnePointAdmissible hc S).nonzero,(degreeOnePointAdmissible hc S).algebraic⟩,
    nonunit_density_point_has_no_ordinary_head_factor c hS h0 hAbs⟩

end IntegrationInACVF.Section7
