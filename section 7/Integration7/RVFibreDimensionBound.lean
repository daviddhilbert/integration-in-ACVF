import Integration7.VolumeAlmostEverywhere
import Section4.RVDimensionRank

/-! The RV dimension of a definable family is bounded by the base
dimension plus a common fibre bound. Coordinate bases and algebraic
parameter elimination avoid any definable choice of fibre maps. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a b : ℕ}

def rvMapFibre {A : DefSet (rawRVSpace (M := M) a) S}
    {B : DefSet (rawRVSpace (M := M) b) S} (f : Map A B) (t : B) :
    DefSet (rawRVSpace (M := M) a) (S ∪ Set.range (rvValues t.val)) :=
  f.fibre t ⟨rvValues t.val,⟨t.val,rfl⟩⟩ (decode_rvValues t.val)

theorem rvDim_le_base_add_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (rawRVSpace (M := M) a) (C.base : Set M)}
    {B : DefSet (rawRVSpace (M := M) b) (C.base : Set M)}
    (f : Map A B) {d j : ℕ} (hB : rvDim B ≤ d)
    (hFibre : ∀ t : B, rvDim (rvMapFibre f t) ≤ j) : rvDim A ≤ d+j := by
  let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
  apply rvDim_le_of_point_rank hc hex C.saturated C.small A (d+j)
  intro x
  let t := f x
  let F := rvMapFibre f t
  let u : F := ⟨x.val,⟨x,rfl,rfl⟩⟩
  obtain ⟨τ,hτ⟩ := exists_rv_coordinate_basis hc hex (C.base : Set M) t.val
  obtain ⟨σ,hσ⟩ := exists_rv_coordinate_basis hc hex
    ((C.base : Set M) ∪ Set.range (rvValues t.val)) x.val
  let w := Fin.append (t.val ∘ τ) (x.val ∘ σ)
  let T := (C.base : Set M) ∪ Set.range (rvValues w)
  have hLeft : Set.range (rvValues (t.val ∘ τ)) ⊆ Set.range (rvValues w) := by
    rintro q ⟨i,rfl⟩
    refine ⟨Fin.castAdd _ i,?_⟩
    simp only [w,rvValues,Fin.append_left,Function.comp_apply]
  have hRight : Set.range (rvValues (x.val ∘ σ)) ⊆ Set.range (rvValues w) := by
    rintro q ⟨i,rfl⟩
    refine ⟨Fin.natAdd _ i,?_⟩
    simp only [w,rvValues,Fin.append_right,Function.comp_apply]
  have hBaseCoords (i : Fin b) : AlgebraicAt T .rv (t.val i).val :=
    (hτ i).mono (Set.union_subset_union_right _ hLeft)
  have hCoords (i : Fin a) : AlgebraicAt T .rv (x.val i).val := by
    apply (hσ i).eliminate_algebraic_params
    rintro q ((hq | ⟨l,rfl⟩) | hq)
    · exact subset_algebraicClosureSet T (Or.inl hq)
    · exact ⟨.rv,hBaseCoords l⟩
    · exact subset_algebraicClosureSet T (Or.inr (hRight hq))
  have hRank := (rvTupleRank_le_of_algebraic hc hex (C.base : Set M) w x.val hCoords).trans
    (rvTupleRank_le_arity hc hex (C.base : Set M) w)
  exact hRank.trans (Nat.add_le_add ((rvTupleRank_le_rvDim hc hex B t).trans hB)
    ((rvTupleRank_le_rvDim hc hex F u).trans (hFibre t)))

theorem rvDim_lt_base_add_positive_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (rawRVSpace (M := M) a) (C.base : Set M)}
    {B : DefSet (rawRVSpace (M := M) b) (C.base : Set M)}
    (f : Map A B) {d k : ℕ} (hB : rvDim B ≤ d)
    (hFibre : ∀ t : B, rvDim (rvMapFibre f t) < k+1) : rvDim A < (d+k)+1 :=
  (rvDim_le_base_add_fibre hc C f hB (fun t => Nat.le_of_lt_succ (hFibre t))).trans_lt
    (Nat.lt_succ_self (d+k))

end IntegrationInACVF.Section7
