import IntegrationSection6.GammaElementaryStructure

/-! Literal domain and volume-graph formulas for the actual elementary
RV blowup. They use the checked old-volume/parameter program, including
its absorbing-zero case. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem elementary_domain_formula (U : RVObject (M := M) S n) (i : Fin n)
    (x : Fin (U.arity+1) → CanonicalRV.RVSort M) :
    x ∈ (elementary U i).domain.carrier ↔
      (fun j => x (Fin.castAdd 1 j)) ∈ U.domain.carrier ∧
      (fun j : Fin 1 => x (Fin.natAdd U.arity j)) ∈ (positiveRV S).carrier := by
  change x ∈ (rvProductDomain U.domain (positiveRV S)).carrier ↔ _
  constructor
  · intro hx
    obtain ⟨u,hu,s,hs,hx⟩ := (mem_rvProductDomain U.domain (positiveRV S) x).mp hx
    have hl : (fun j => x (Fin.castAdd 1 j)) = u := by
      funext j
      exact (congrFun hx (Fin.castAdd 1 j)).symm.trans (Fin.append_left _ _ j)
    have hr : (fun j : Fin 1 => x (Fin.natAdd U.arity j)) = s := by
      funext j
      exact (congrFun hx (Fin.natAdd U.arity j)).symm.trans (Fin.append_right _ _ j)
    exact ⟨hl.symm ▸ hu,hr.symm ▸ hs⟩
  · rintro ⟨hu,hs⟩
    apply (mem_rvProductDomain U.domain (positiveRV S) x).mpr
    refine ⟨fun j => x (Fin.castAdd 1 j),hu,fun j => x (Fin.natAdd U.arity j),hs,?_⟩
    change Fin.append (fun j => x (Fin.castAdd 1 j)) (fun j => x (Fin.natAdd U.arity j)) = x
    exact Fin.append_castAdd_natAdd

theorem elementary_graph_formula (U : RVObject (M := M) S n) (i : Fin n)
    (x : Fin (U.arity+1) → CanonicalRV.RVSort M) (y : Fin n → CanonicalRV.RVSort M) :
    (∃ w : (elementary U i).domain, w.val = x ∧ ((elementary U i).volume w).val = y) ↔
      x ∈ (elementary U i).domain.carrier ∧
      ∃ u : U.domain, u.val = (fun j => x (Fin.castAdd 1 j)) ∧
        (oldVolumeParameterBlowupMap S i ⟨Fin.append (U.volume u).val
          (fun j => x (Fin.natAdd U.arity j)),Set.mem_univ _⟩).val = y := by
  constructor
  · rintro ⟨w,rfl,hy⟩
    have hp := elementaryVolume_oldProgram U i w
    rw [elementaryOldVolumeParamMap_value,elementaryParameter_labels] at hp
    exact ⟨w.property,elementaryProjection U i w,elementaryProjection_labels U i w,hp.symm.trans hy⟩
  · rintro ⟨hx,u,hu,hy⟩
    let w : (elementary U i).domain := ⟨x,hx⟩
    have hproj : elementaryProjection U i w = u :=
      Subtype.ext ((elementaryProjection_labels U i w).trans hu.symm)
    have hp := elementaryVolume_oldProgram U i w
    rw [elementaryOldVolumeParamMap_value,elementaryParameter_labels,hproj] at hp
    exact ⟨w,rfl,hp.trans hy⟩

end IntegrationInACVF.Section6
