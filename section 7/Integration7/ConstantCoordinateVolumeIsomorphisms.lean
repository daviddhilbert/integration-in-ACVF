module

public import Integration7.LowerDimensionRVVolumeIsomorphisms
public import Integration7.RVCoordinateSelection
public import Integration7.NondegenerateFiniteIso

@[expose] public section

/-! A finite RV[2] object with one constant volume coordinate has RV
dimension at most one. Consequently equal densities and equal products
of Gamma coordinates suffice for its actual volume isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n d k : ℕ}

theorem finite_volume_dimension_le_selected
    (U : RVFiniteObject (M := M) S n) (ρ : Fin d → Fin n)
    (hDetermines : ∀ p q : U.obj.domain, U.obj.value p ∘ ρ = U.obj.value q ∘ ρ →
      U.obj.value p = U.obj.value q) : rvDim U.obj.domain ≤ d := by
  let F := Map.comp (rvCoordinateSelectMap S ρ) U.obj.volume
  apply (rvDim_le_iff U.obj.domain d).mpr
  refine ⟨d,le_rfl,F,?_⟩
  intro z
  by_cases h : ∃ u, F u = z
  · obtain ⟨u,hu⟩ := h
    apply (U.property (U.obj.volume u)).subset
    intro q hq
    apply Subtype.ext
    apply hDetermines
    exact congrArg Subtype.val (hq.trans hu.symm)
  · have he : {u | F u = z} = ∅ := by
      ext u
      exact ⟨fun hu => (h ⟨u,hu⟩).elim,False.elim⟩
    rw [he]
    exact Set.finite_empty

theorem constant_head_volume_dimension_le_one
    (U : RVFiniteObject (M := M) S 2) (r : CanonicalRV.RVSort M)
    (hHead : ∀ u, U.obj.value u 0 = r) : rvDim U.obj.domain ≤ 1 := by
  apply finite_volume_dimension_le_selected U (fun _ : Fin 1 => (1 : Fin 2))
  intro p q he
  funext j
  fin_cases j
  · exact (hHead p).trans (hHead q).symm
  · exact congrFun he 0

theorem constant_tail_volume_dimension_le_one
    (U : RVFiniteObject (M := M) S 2) (t : CanonicalRV.RVSort M)
    (hTail : ∀ u, U.obj.value u 1 = t) : rvDim U.obj.domain ≤ 1 := by
  apply finite_volume_dimension_le_selected U (fun _ : Fin 1 => (0 : Fin 2))
  intro p q he
  funext j
  fin_cases j
  · exact congrFun he 0
  · exact (hTail p).trans (hTail q).symm

def RVVolumeIso.of_gamma_product_of_lower_dimension
    {U V : PositiveRVVolumeObject (M := M) S k} (e : U.essential ≅ V.essential)
    (hd : rvDim U.essential.obj.domain < k+1)
    (hDensity : ∀ u, U.essentialForm.value u = V.essentialForm.value (finiteIsoMap e u))
    (hProduct : ∀ u, (∏ i, Values.vrv (U.essential.obj.value u i)) =
      ∏ i, Values.vrv (V.essential.obj.value (finiteIsoMap e u) i)) : RVVolumeIso U V := by
  apply RVVolumeIso.of_gamma_of_lower_rvDim e hd
  intro u
  have hGamma : rvVolumeGamma (U.essential.obj.value u) (U.essential_nonzero u) =
      rvVolumeGamma (V.essential.obj.value (finiteIsoMap e u)) (V.essential_nonzero (finiteIsoMap e u)) := by
    apply Subtype.ext
    change Values.gammaValHom _ = Values.gammaValHom _
    rw [rvVolumeGamma,rvVolumeGamma,map_prod,map_prod]
    exact hProduct u
  have hJ : rvGammaJacobian (U.essential.obj.value u)
      (V.essential.obj.value (finiteIsoMap e u)) (U.essential_nonzero u)
      (V.essential_nonzero (finiteIsoMap e u)) = 1 :=
    (congrArg (fun z : Values.Gamma (M := M) =>
      rvVolumeGamma (V.essential.obj.value (finiteIsoMap e u)) (V.essential_nonzero (finiteIsoMap e u))/z)
      hGamma).trans (by simp)
  rw [hJ,Values.gamma_val_one,mul_one]
  exact congrArg Values.vrv (hDensity u)

def constantHeadVolumeIso
    {U V : PositiveRVVolumeObject (M := M) S 1} (e : U.essential ≅ V.essential)
    (r : CanonicalRV.RVSort M) (hHead : ∀ u, U.essential.obj.value u 0 = r)
    (hDensity : ∀ u, U.essentialForm.value u = V.essentialForm.value (finiteIsoMap e u))
    (hProduct : ∀ u, Values.vrv (U.essential.obj.value u 0)*Values.vrv (U.essential.obj.value u 1) =
      Values.vrv (V.essential.obj.value (finiteIsoMap e u) 0)*Values.vrv (V.essential.obj.value (finiteIsoMap e u) 1)) :
    RVVolumeIso U V := by
  apply RVVolumeIso.of_gamma_product_of_lower_dimension e
    (lt_of_le_of_lt (constant_head_volume_dimension_le_one U.essential r hHead) (by decide)) hDensity
  intro u
  change (∏ i : Fin 2, Values.vrv (U.essential.obj.value u i)) =
    ∏ i : Fin 2, Values.vrv (V.essential.obj.value (finiteIsoMap e u) i)
  rw [Fin.prod_univ_two,Fin.prod_univ_two]
  exact hProduct u

end IntegrationInACVF.Section7
