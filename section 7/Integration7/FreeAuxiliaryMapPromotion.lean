module

public import Integration7.FiniteAuxiliaryMapPromotion
public import Section3.SortedTuples

@[expose] public section

/-! A finite RV exception map in any real context has a formula
presentation after naming finitely many sorted auxiliary parameters.
No equation identifying the whole context with a named term closure is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a j : ℕ} {sp : Fin p → SortTag}

theorem finite_auxiliary_map_promotion_free {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (D : DefSet (rawRVSpace (M := M) a) S)
    (g : Map D (DefSet.univ (rawRVSpace (M := M) j) S)) (hg : g.FiniteFibres) :
    ∃ q : ℕ, ∃ sq : Fin q → SortTag, ∃ y : Fin q → M,
      (∀ i, sortEval (sq i) (y i)) ∧
      ∃ E : GammaFiniteRVSchema B (p+q) a j (Fin.append sp sq),
        E.valid (Fin.append z y) ∧
          ∀ w, w ∈ D.carrier ↔ Fin.append (Fin.append z y) (rvValues w) ∈ E.domain := by
  obtain ⟨FD, _, hFD⟩ := Set.definable_iff_finitely_definable.mp D.definable
  obtain ⟨FG, _, hFG⟩ := Set.definable_iff_finitely_definable.mp
    (rawRVRelationFormula_definable g.graph_definable)
  let F := FD ∪ FG
  let eF : F ≃ Fin F.card := Finset.equivFin F
  let y (i : Fin F.card) : M := (eF.symm i).val
  let sq (i : Fin F.card) : SortTag := if iVF (y i) then .vf else .rv
  have hy (i : Fin F.card) : sortEval (sq i) (y i) := by
    by_cases hi : iVF (y i)
    · dsimp only [sq]
      rw [if_pos hi]
      exact hi
    · dsimp only [sq]
      rw [if_neg hi]
      exact (TypedModelMap.sort_cover (M := M) (y i)).resolve_left hi
  let T := B.real ∪ Set.range (Fin.append z y)
  have hFT : (F : Set M) ⊆ T := by
    intro x hx
    refine Or.inr ⟨Fin.natAdd p (eF ⟨x,hx⟩), ?_⟩
    rw [Fin.append_right]
    change (eF.symm (eF ⟨x,hx⟩)).val = x
    rw [eF.symm_apply_apply]
  have hD : T.Definable LRV ((rawRVSpace (M := M) a).preimage D.carrier) :=
    hFD.mono (fun x hx => hFT (Finset.mem_union.mpr (Or.inl hx)))
  have hG : T.Definable LRV (rawRVRelationFormula g.graph) :=
    hFG.mono (fun x hx => hFT (Finset.mem_union.mpr (Or.inr hx)))
  obtain ⟨P⟩ := realFiniteMap_gammaPresentation (B := ⟨T,B.gamma⟩) hc D g hg hD hG
  have hzy (i) : sortEval (Fin.append sp sq i) (Fin.append z y i) := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hz i
    · simpa only [Fin.append_right] using hy i
  obtain ⟨E,hE,hED,_⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma
    (Fin.append sp sq) (Fin.append z y) hzy P.toGamma
  refine ⟨F.card,sq,y,hy,E,hE,?_⟩
  intro w
  rw [hED]
  constructor
  · intro hw
    exact ⟨⟨w,(Set.ext_iff.mp P.domain_eq w).mpr hw⟩,rfl⟩
  · rintro ⟨u,hu⟩
    have he : u.val = w := funext (fun i => Subtype.ext (congrFun hu i))
    exact he ▸ (Set.ext_iff.mp P.domain_eq u.val).mp u.property

end IntegrationInACVF.Section7
