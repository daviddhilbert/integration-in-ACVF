import Integration7.RVVolumeMorphisms
import Section4.RVCoordinates

/-! Exact raw-tuple formulas for actual RV domains and relations. These
are ordinary real definability bridges and retain every RV coordinate. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] {S : Set M} {a b : ℕ}

def rawRVRelationFormula
    (R : (Fin a → CanonicalRV.RVSort M) → (Fin b → CanonicalRV.RVSort M) → Prop) :
    Set (Fin (a+b) → M) :=
  {w | w ∘ Sum.elim (Fin.castAdd b) (Fin.natAdd a) ∈
    (rawRVSpace (M := M) a).relation (rawRVSpace (M := M) b) R}

theorem rawRVRelationFormula_definable
    {R : (Fin a → CanonicalRV.RVSort M) → (Fin b → CanonicalRV.RVSort M) → Prop}
    (hR : (rawRVSpace (M := M) a).RelationDefinable (rawRVSpace (M := M) b) S R) :
    S.Definable LRV (rawRVRelationFormula R) :=
  hR.preimage_comp (Sum.elim (Fin.castAdd b) (Fin.natAdd a))

theorem rawRVRelationFormula_append
    (R : (Fin a → CanonicalRV.RVSort M) → (Fin b → CanonicalRV.RVSort M) → Prop)
    (x : Fin a → CanonicalRV.RVSort M) (y : Fin b → CanonicalRV.RVSort M) :
    Fin.append (rvValues x) (rvValues y) ∈ rawRVRelationFormula R ↔ R x y := by
  have he : Fin.append (rvValues x) (rvValues y) ∘ Sum.elim (Fin.castAdd b) (Fin.natAdd a) =
      Sum.elim (rvValues x) (rvValues y) := by
    funext i
    cases i <;> simp only [Function.comp_apply,Sum.elim_inl,Sum.elim_inr,Fin.append_left,Fin.append_right]
  change (_ ∈ (rawRVSpace (M := M) a).relation (rawRVSpace (M := M) b) R) ↔ R x y
  rw [he]
  have h := Space.relation_decode (rawRVSpace (M := M) a) (rawRVSpace (M := M) b) R
    ⟨rvValues x,⟨x,rfl⟩⟩ ⟨rvValues y,⟨y,rfl⟩⟩
  simp only [decode_rvValues] at h
  change (Sum.elim (rvValues x) (rvValues y) ∈
    (rawRVSpace (M := M) a).relation (rawRVSpace (M := M) b) R) ↔ R x y at h
  change (Sum.elim (rvValues x) (rvValues y) ∈
    (rawRVSpace (M := M) a).relation (rawRVSpace (M := M) b) R) ↔ R x y
  exact h

theorem rawRVRelationFormula_proper
    (R : (Fin a → CanonicalRV.RVSort M) → (Fin b → CanonicalRV.RVSort M) → Prop)
    (w : Fin (a+b) → M) (hw : w ∈ rawRVRelationFormula R) : ∀ i, iRV (w i) := by
  obtain ⟨hx,hy,_⟩ := hw
  obtain ⟨x,hx⟩ := hx
  obtain ⟨y,hy⟩ := hy
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have h := congrFun hx i
    change (x i).val = w (Fin.castAdd b i) at h
    exact h ▸ (x i).property
  · have h := congrFun hy i
    change (y i).val = w (Fin.natAdd a i) at h
    exact h ▸ (y i).property

end IntegrationInACVF.Section7
