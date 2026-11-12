import IntegrationSection6.TupleBlockSwap

/-! First-order validity of finite-volume map schemata. Totality, unique
outputs, the exact source locus and a fixed finite bound on reverse fibres
are all expressed over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

def finiteMapRowValid (sp : Fin p → SortTag) (sy : Fin k → SortTag)
    (D : Set (Fin (p+a) → M)) (V : Set (Fin ((p+a)+k) → M)) (N : ℕ) (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧
  (∀ x : Fin a → M, Fin.append z x ∈ D → ∃! y : Fin k → M, Fin.append (Fin.append z x) y ∈ V) ∧
  (∀ x : Fin a → M, ∀ y : Fin k → M, Fin.append (Fin.append z x) y ∈ V → Fin.append z x ∈ D) ∧
  (∀ y : Fin k → M, (∀ j, sortEval (sy j) (y j)) →
    {x : Fin a → M | Fin.append (Fin.append z x) y ∈ V}.Finite ∧
    {x : Fin a → M | Fin.append (Fin.append z x) y ∈ V}.ncard ≤ N)

theorem gamma_finite_map_validity_definable (sp : Fin p → SortTag) (sx : Fin a → SortTag)
    (sy : Fin k → SortTag) (N : ℕ)
    {D : Set (Fin (p+a) → M)} {V : Set (Fin ((p+a)+k) → M)}
    (hD : DefinableOverBase B (Fin.append sp sx) D)
    (hV : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) V) :
    DefinableOverBase B sp {z | finiteMapRowValid sp sy D V N z} := by
  have hUnique := gamma_family_row_unique_definable (Fin.append sp sx) sy hV
  have hTotal := gamma_family_row_subset_definable sp sx hD hUnique
  have hExists := gamma_family_row_exists_definable (Fin.append sp sx) sy hV
  have hSource := gamma_family_row_subset_definable sp sx hExists hD
  let W := (fun v => v ∘ swapLastBlockCoordinates p a k) '' V
  have hW : DefinableOverBase B (Fin.append (Fin.append sp sy) sx) W := by
    have h := hV.image_real (swapLastBlockCoordinates p a k)
    rw [append_swapLastBlocks] at h
    exact h
  have hBound := gamma_family_finite_bound_definable (Fin.append sp sy) sx N hW
  have hAll := gamma_family_row_forall_definable sp sy hBound
  have h := hTotal.inter (hSource.inter hAll)
  have hRows (z : Fin p → M) (y : Fin k → M) :
      {x : Fin a → M | Fin.append (Fin.append z y) x ∈ W} =
      {x : Fin a → M | Fin.append (Fin.append z x) y ∈ V} := by
    apply Set.ext
    intro x
    exact append_mem_swapLastBlocks_image V z x y
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hs,ht,hd,hf⟩
    refine ⟨⟨hs,ht⟩,⟨hs,?_⟩,hs,?_⟩
    · rintro x ⟨y,hy⟩
      exact hd x y hy
    · intro y hy
      refine ⟨?_,?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.append_left] using hs j
        · simpa only [Fin.append_right] using hy j
      · rw [hRows]
        exact hf y hy
  · rintro ⟨⟨hs,ht⟩,⟨_,hd⟩,_,hf⟩
    refine ⟨hs,ht,fun x y hxy => hd x ⟨y,hxy⟩,?_⟩
    intro y hy
    have h := (hf y hy).2
    rw [hRows] at h
    exact h

end IntegrationInACVF.Section6
