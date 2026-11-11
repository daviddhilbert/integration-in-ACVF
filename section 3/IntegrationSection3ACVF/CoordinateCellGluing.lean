import IntegrationSection3ACVF.CoordinatePartitionTemplates

/-! Glue one scalar cell over one context case using the full partial
map graph. No definability of the total map outside its domain is used. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.CoordinateCellGluing

open CoordinateSlices CoordinateFibres CoordinateFibreSyntax
open ParameterizedOpenImages PromotedPartitionTemplates

variable {M ι τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def context (f : (ι → M) → (τ → M)) (i : ι) (j : τ) (x : ι → M) : Params i j → M :=
  Sum.elim (tail i x) (tail j (f x))

def piece (A : Set (ι → M)) (f : (ι → M) → (τ → M)) (i : ι) (j : τ)
    (U : Set (Params i j → M)) (C : Set (Params i j ⊕ Fin 1 → M)) : Set (ι → M) :=
  {x | x ∈ A ∧ context f i j x ∈ U ∧ Sum.elim (context f i j x) ![x i] ∈ C}

theorem piece_definable [Finite ι] [Finite τ] (B : FullBaseAtomicity.Base (M := M))
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f)) (i : ι) (j : τ)
    {U : Set (Params i j → M)} (hU : FullBaseAtomicity.OverBase B U)
    {C : Set (Params i j ⊕ Fin 1 → M)} (hC : FullBaseAtomicity.OverBase B C) :
    FullBaseAtomicity.OverBase B (piece A f i j U C) := by
  let πU : Params i j → ι ⊕ τ := Sum.elim (fun k => .inl k.val) (fun k => .inr k.val)
  let πC : Params i j ⊕ Fin 1 → ι ⊕ τ := Sum.elim πU (fun _ => .inl i)
  have heU (x : ι → M) (y : τ → M) :
      Sum.elim x y ∘ πU = Sum.elim (tail i x) (tail j y) := by
    funext k
    cases k <;> rfl
  have heC (x : ι → M) (y : τ → M) :
      Sum.elim x y ∘ πC = Sum.elim (Sum.elim (tail i x) (tail j y)) ![x i] := by
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => fin_cases k; rfl
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hf
    (FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.preimage_comp hU πU)
      (FullBaseAtomicity.OverBase.preimage_comp hC πC)))
  apply FullBaseAtomicity.OverBase.congr hd
  intro x
  change (∃ y : τ → M, (x ∈ A ∧ y = f x) ∧ Sum.elim x y ∘ πU ∈ U ∧ Sum.elim x y ∘ πC ∈ C) ↔ _
  simp_rw [heU,heC]
  exact ⟨fun ⟨_,⟨hx,rfl⟩,hU,hC⟩ => ⟨hx,hU,hC⟩,fun ⟨hx,hU,hC⟩ => ⟨f x,⟨hx,rfl⟩,hU,hC⟩⟩

theorem mem_source_piece (A : Set (ι → M)) (f : (ι → M) → (τ → M)) (i : ι) (j : τ)
    (U : Set (Params i j → M)) (C : Set (Params i j ⊕ Fin 1 → M))
    (u : Other i → M) (v : Other j → M) (t : M) :
    t ∈ source (piece A f i j U C) f i j u v ↔
      t ∈ source A f i j u v ∧ Sum.elim u v ∈ U ∧ t ∈ fibre C (Sum.elim u v) := by
  have hCtx (h : tail j (f (insert i u t)) = v) :
      context f i j (insert i u t) = Sum.elim u v := by
    unfold context
    rw [tail_insert,h]
  constructor
  · rintro ⟨⟨hA,hU,hC⟩,hOut⟩
    rw [hCtx hOut] at hU hC
    rw [insert_same] at hC
    exact ⟨⟨hA,hOut⟩,hU,hC⟩
  · rintro ⟨⟨hA,hOut⟩,hU,hC⟩
    refine ⟨⟨hA,?_,?_⟩,hOut⟩
    · rwa [hCtx hOut]
    · rw [hCtx hOut,insert_same]
      exact hC

theorem piece_openToOpen (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hinj : Set.InjOn f A) (i : ι) (j : τ)
    (U : Set (Params i j → M)) (T : Template M (Params i j))
    (hU : U ⊆ locus (CoordinatePartitionTemplates.graph A f i j) T) (k : Fin T.size) :
    CoordinateOpenToOpen.At (piece A f i j U (T.cell k)) f i j := by
  intro u v
  let p : Params i j → M := Sum.elim u v
  let D := source A f i j u v
  let g := map f i j u
  by_cases hp : p ∈ U
  · have hValid := (UnaryPartitionTemplates.valid_iff
      (CoordinatePartitionTemplates.graph A f i j) T.cell p D g (fun _ _ => Iff.rfl)
      (map_injOn f hinj i j u v)).mp (hU hp)
    have he : source (piece A f i j U (T.cell k)) f i j u v = fibre (T.cell k) p := by
      ext t
      rw [mem_source_piece]
      constructor
      · exact fun h => h.2.2
      · intro ht
        exact ⟨(hValid.1 t).mpr ⟨k,ht⟩,hp,ht⟩
    rw [he]
    exact hValid.2.2 k
  · have he : source (piece A f i j U (T.cell k)) f i j u v = ∅ := by
      ext t
      rw [mem_source_piece]
      exact ⟨fun h => (hp h.2.1).elim,fun h => h.elim⟩
    rw [he]
    intro D hD
    have hDE : D = ∅ := Set.Subset.antisymm hD (Set.empty_subset _)
    rw [hDE,Set.image_empty]

end IntegrationInACVF.Section3ACVF.CoordinateCellGluing
