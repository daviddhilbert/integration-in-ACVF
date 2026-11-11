import IntegrationSection4.FiniteScalarFamilies

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FiniteImageFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A family with finite scalar images has a uniform finite-arity RV
refinement on whose fibres its value is constant. -/
theorem exists_refinement {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) {n : ℕ}
    (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (hfVF : ∀ p x, x ∈ A p → iVF (f p x)) (hf : FiniteScalarFamilies.Graph B A f)
    (hFin : ∀ p, (f p '' A p).Finite) :
    ∃ d : ℕ, ∃ e : (Fin n → M) → M → Fin d → M,
      (∀ p x, x ∈ A p → ∀ i, iRV (e p x i)) ∧
      FullBaseAtomicity.OverBase B {z : (Fin n ⊕ Fin 1) ⊕ Fin d → M |
        z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
          z ∘ Sum.inr = e (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))} ∧
      ∀ p x, x ∈ A p → ∀ y, y ∈ A p → e p x = e p y → f p x = f p y := by
  have hPre (p : Fin n → M) : {y : VFType (M := M) | y.val ∈ f p '' A p}.Finite :=
    (hFin p).preimage Subtype.val_injective.injOn
  let F (p : Fin n → M) : Finset (VFType (M := M)) := (hPre p).toFinset
  have hMem (p : Fin n → M) (y : VFType (M := M)) : y ∈ F p ↔ y.val ∈ f p '' A p :=
    (hPre p).mem_toFinset
  let π : (Fin n ⊕ Fin 1) ⊕ Fin 1 → (Fin n ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (Sum.elim (fun i => .inl (.inl i)) Sum.inr) (fun _ => .inl (.inr 0))
  have hF : FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M |
      ∃ y ∈ F (z ∘ Sum.inl), y.val = z (.inr 0)} := by
    have hh := FullBaseAtomicity.OverBase.exists_block
      (FullBaseAtomicity.OverBase.preimage_comp hf π)
    apply FullBaseAtomicity.OverBase.congr hh
    intro z
    change (∃ x : Fin 1 → M, x 0 ∈ A (z ∘ Sum.inl) ∧ z (.inr 0) = f (z ∘ Sum.inl) (x 0)) ↔ _
    constructor
    · rintro ⟨x,hx,he⟩
      refine ⟨⟨z (.inr 0),he ▸ hfVF _ _ hx⟩,?_,rfl⟩
      exact (hMem _ _).mpr ⟨x 0,hx,he.symm⟩
    · rintro ⟨y,hy,he⟩
      obtain ⟨x,hx,hxy⟩ := (hMem _ _).mp hy
      exact ⟨![x],hx,he ▸ hxy.symm⟩
  obtain ⟨d,hBound⟩ := FullBaseFiniteBounds.uniform_bound hκ hs B hsmall F hF
  let e (p : Fin n → M) (x : M) : Fin d → M := FullBaseFiniteCodes.code d F p (f p x)
  have hCode := FullBaseFunctions.tuple_graph B (fun i : Fin d =>
    FullBaseFiniteCodes.code_graph B h00 d F hF d hBound i)
  let ι := ((Fin n ⊕ Fin 1) ⊕ Fin d) ⊕ Fin 1
  have hFun := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (fun i => .inl (.inl i)) Sum.inr : (Fin n ⊕ Fin 1) ⊕ Fin 1 → ι)
  have hCode' := FullBaseAtomicity.OverBase.preimage_comp hCode
    (Sum.elim (Sum.elim (fun i => .inl (.inl (.inl i))) Sum.inr)
      (fun i => .inl (.inr i)) : (Fin n ⊕ Fin 1) ⊕ Fin d → ι)
  have hE : FullBaseAtomicity.OverBase B {z : (Fin n ⊕ Fin 1) ⊕ Fin d → M |
      z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
        z ∘ Sum.inr = e (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))} := by
    have hh := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hFun hCode')
    apply FullBaseAtomicity.OverBase.congr hh
    intro z
    change (∃ y : Fin 1 → M,
      (z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
        y 0 = f (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))) ∧
      z ∘ Sum.inr = FullBaseFiniteCodes.code d F (z ∘ Sum.inl ∘ Sum.inl) (y 0)) ↔ _
    constructor
    · rintro ⟨y,⟨hx,hy⟩,he⟩
      exact ⟨hx,by simpa only [hy] using he⟩
    · rintro ⟨hx,he⟩
      exact ⟨![f (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))],⟨hx,rfl⟩,he⟩
  refine ⟨d,e,?_,hE,?_⟩
  · intro p x hx i
    exact FullBaseFiniteCodes.code_sorted d F p ⟨f p x,hfVF p x hx⟩ i
  · intro p x hx y hy he
    let X : VFType (M := M) := ⟨f p x,hfVF p x hx⟩
    let Y : VFType (M := M) := ⟨f p y,hfVF p y hy⟩
    have hX : X ∈ F p := (hMem p X).mpr ⟨x,hx,rfl⟩
    have hY : Y ∈ F p := (hMem p Y).mpr ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (FullBaseFiniteCodes.code_injective h00 d F hBound p hX hY he)

end IntegrationInACVF.Section4.FiniteImageFamilies
