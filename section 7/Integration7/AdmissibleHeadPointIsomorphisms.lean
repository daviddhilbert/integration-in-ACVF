module

public import Integration7.AdmissibleHeadPointMaps
public import Integration7.EssentialFiniteBijections
public import Integration7.LowerDimensionRVVolumeIsomorphisms
public import Integration7.FiniteVolumeCertificateCriterion

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! In positive remaining degree the admissible object is genuinely
isomorphic, with both volume equations, to its head factor times the
degree-one point. Admissibility makes the RV equation lower dimensional. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem admissible_head_point_preserves_essential
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) (u : U.underlying.obj.domain) :
    u.val ∈ (rvEssentialLabels U.underlying.obj).carrier ↔
      (admissibleHeadPointMap C U h u).val ∈
        (rvEssentialLabels ((admissibleHeadVolumeFactor C U h).prod
          (degreeOnePointVolumeObject (C.base : Set M))).underlying.obj).carrier := by
  rw [mem_rvEssentialLabels,mem_rvEssentialLabels,admissible_head_point_map_coordinates]
  constructor
  · intro hu j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left,Function.comp_apply] using hu i.castSucc
    · rw [Fin.append_right]
      exact (rv_nonzero_iff_raw _).mp one_ne_zero
  · intro hu j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact (rv_nonzero_iff_raw _).mp (h.nonzero u)
    · simpa only [Fin.append_left,Function.comp_apply] using hu (Fin.castAdd 1 i)

theorem admissible_essential_dimension_lt
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (h : BlowupAdmissible U) : rvDim U.essential.obj.domain < k+1 := by
  let H := admissibleHeadFiniteObject C U h
  let f := H.obj.volume.restrict (rvEssentialLabels_subset U.underlying.obj)
  have hf : f.FiniteFibres := by
    intro t
    apply (H.property t).of_injOn (f := fun u : U.essential.obj.domain =>
      (⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩ : H.obj.domain))
    · intro u hu
      exact hu
    · intro u hu v hv he
      exact Subtype.ext (congrArg (fun z : H.obj.domain => z.val) he)
  exact Nat.lt_succ_of_le ((rvDim_le_iff U.essential.obj.domain k).mpr ⟨k,le_rfl,f,hf⟩)

def admissibleHeadPointVolumeIso
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) :
    RVVolumeIso U ((admissibleHeadVolumeFactor C U h).prod (degreeOnePointVolumeObject (C.base : Set M))) := by
  let V := (admissibleHeadVolumeFactor C U h).prod (degreeOnePointVolumeObject (C.base : Set M))
  let e : U.essential ≅ V.essential := finiteEssentialIsoOfFullBijection (admissibleHeadPointMap C U h)
    (admissible_head_point_map_bijective C U h) (admissible_head_point_preserves_essential C U h)
  apply RVVolumeIso.of_gamma_of_lower_rvDim e (admissible_essential_dimension_lt C U h)
  intro u
  apply gammaVolumeEquation_of_weight e u
  let u0 : U.underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩
  change RVOperations.absoluteHom (U.form.value u0) * (∏ i, RVOperations.absoluteHom (U.underlying.obj.value u0 i)) =
    RVOperations.absoluteHom (V.form.value (admissibleHeadPointMap C U h u0)) *
      (∏ i, RVOperations.absoluteHom (V.underlying.obj.value (admissibleHeadPointMap C U h u0) i))
  rw [admissible_head_point_map_density,admissible_head_point_map_coordinates,map_mul]
  have ht : (∏ i : Fin ((k+1)+1), RVOperations.absoluteHom
      (Fin.append (U.underlying.obj.value u0 ∘ Fin.castSucc) (fun _ : Fin 1 => 1) i)) =
      ∏ i : Fin (k+1), RVOperations.absoluteHom (U.underlying.obj.value u0 i.castSucc) := by
    simpa only [Fin.append_left,Fin.append_right,Fin.prod_univ_one,map_one,mul_one,Function.comp_apply]
      using Fin.prod_univ_add (a := k+1) (b := 1) (fun i => RVOperations.absoluteHom
        (Fin.append (U.underlying.obj.value u0 ∘ Fin.castSucc) (fun _ : Fin 1 => 1) i))
  rw [ht,Fin.prod_univ_castSucc]
  ac_rfl

end IntegrationInACVF.Section7
