import IntegrationSection4.FullBaseFiniteCodes
import IntegrationSection4.FullBaseFiniteBounds

/-! Uniform RV refinements of finite scalar fibres. Free parameters remain
variables throughout; the exported graph uses the unchanged full base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FiniteScalarFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Graph {n : ℕ} (B : FullBaseAtomicity.Base (M := M))
    (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M) : Prop :=
  FullBaseAtomicity.OverBase B {z : (Fin n ⊕ Fin 1) ⊕ Fin 1 → M |
    z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
      z (.inr 0) = f (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))}

theorem domain_definable {n : ℕ} (B : FullBaseAtomicity.Base (M := M))
    (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M) (hf : Graph B A f) :
    FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ A (z ∘ Sum.inl)} := by
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.exists_block hf)
  intro z
  change (∃ y : Fin 1 → M, z (.inr 0) ∈ A (z ∘ Sum.inl) ∧ y 0 = f (z ∘ Sum.inl) (z (.inr 0))) ↔ _
  exact ⟨fun ⟨_,h,_⟩ => h,fun h => ⟨![f (z ∘ Sum.inl) (z (.inr 0))],h,rfl⟩⟩

theorem restrict {n : ℕ} (B : FullBaseAtomicity.Base (M := M))
    (A D : (Fin n → M) → Set M) (f : (Fin n → M) → M → M) (hf : Graph B A f)
    (hD : FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ D (z ∘ Sum.inl)})
    (hDA : ∀ p, D p ⊆ A p) : Graph B D f := by
  have hh := FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hD (Sum.inl : Fin n ⊕ Fin 1 → (Fin n ⊕ Fin 1) ⊕ Fin 1)) hf
  apply FullBaseAtomicity.OverBase.congr hh
  intro z
  change (z (.inl (.inr 0)) ∈ D (z ∘ Sum.inl ∘ Sum.inl) ∧
    z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
    z (.inr 0) = f (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))) ↔ _
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hDA _ h.1,h.2⟩⟩

/-- Finitely many intrinsic RV coordinates distinguish points in each
finite function fibre, uniformly in all free parameters. -/
theorem exists_refinement {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) {n : ℕ}
    (A : (Fin n → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin n → M) → M → M) (hf : Graph B A f)
    (hFin : ∀ p y, {x | x ∈ A p ∧ f p x = y}.Finite) :
    ∃ d : ℕ, ∃ e : (Fin n → M) → M → Fin d → M,
      (∀ p x, ∀ i, iVF x → iRV (e p x i)) ∧
      FullBaseAtomicity.OverBase B {z : (Fin n ⊕ Fin 1) ⊕ Fin d → M |
        z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
          z ∘ Sum.inr = e (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))} ∧
      ∀ p x, x ∈ A p → ∀ y, y ∈ A p → f p x = f p y → e p x = e p y → x = y := by
  have hPre (t : Fin (n+1) → M) :
      {x : VFType (M := M) | x.val ∈ A (Fin.init t) ∧ f (Fin.init t) x.val = t (Fin.last n)}.Finite :=
    (hFin (Fin.init t) (t (Fin.last n))).preimage Subtype.val_injective.injOn
  let F (t : Fin (n+1) → M) : Finset (VFType (M := M)) := (hPre t).toFinset
  have hMem (t : Fin (n+1) → M) (x : VFType (M := M)) :
      x ∈ F t ↔ x.val ∈ A (Fin.init t) ∧ f (Fin.init t) x.val = t (Fin.last n) :=
    (hPre t).mem_toFinset
  let π : (Fin n ⊕ Fin 1) ⊕ Fin 1 → Fin (n+1) ⊕ Fin 1 :=
    Sum.elim (Sum.elim (fun i => .inl i.castSucc) (fun _ => .inr 0)) (fun _ => .inl (Fin.last n))
  have hF : FullBaseAtomicity.OverBase B {z : Fin (n+1) ⊕ Fin 1 → M |
      ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)} := by
    have hh := FullBaseAtomicity.OverBase.preimage_comp hf π
    apply FullBaseAtomicity.OverBase.congr hh
    intro z
    change (z (.inr 0) ∈ A (Fin.init (z ∘ Sum.inl)) ∧
      z (.inl (Fin.last n)) = f (Fin.init (z ∘ Sum.inl)) (z (.inr 0))) ↔ _
    constructor
    · intro h
      exact ⟨⟨z (.inr 0),hAVF _ h.1⟩,(hMem _ _).mpr ⟨h.1,h.2.symm⟩,rfl⟩
    · rintro ⟨x,hx,he⟩
      have hh := (hMem _ _).mp hx
      rw [he] at hh
      exact ⟨hh.1,hh.2.symm⟩
  obtain ⟨d,hBound⟩ := FullBaseFiniteBounds.uniform_bound hκ hs B hsmall F hF
  let e (p : Fin n → M) (x : M) : Fin d → M :=
    FullBaseFiniteCodes.code d F (Fin.snoc p (f p x)) x
  have hCode := FullBaseFunctions.tuple_graph B (fun i : Fin d =>
    FullBaseFiniteCodes.code_graph B h00 d F hF d hBound i)
  let ι := ((Fin n ⊕ Fin 1) ⊕ Fin d) ⊕ Fin 1
  let ρ : (Fin n ⊕ Fin 1) ⊕ Fin 1 → ι :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  have hFun := FullBaseAtomicity.OverBase.preimage_comp hf ρ
  let σ : (Fin (n+1) ⊕ Fin 1) ⊕ Fin d → ι :=
    Sum.elim (Sum.elim
      (Fin.lastCases (.inr 0) (fun i => .inl (.inl (.inl i))))
      (fun _ => .inl (.inl (.inr 0)))) (fun i => .inl (.inr i))
  have hCode' := FullBaseAtomicity.OverBase.preimage_comp hCode σ
  have hE : FullBaseAtomicity.OverBase B {z : (Fin n ⊕ Fin 1) ⊕ Fin d → M |
      z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
        z ∘ Sum.inr = e (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))} := by
    have hh := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hFun hCode')
    apply FullBaseAtomicity.OverBase.congr hh
    intro z
    have hparam (y : Fin 1 → M) :
        (fun i : Fin (n+1) => Sum.elim z y (σ (.inl (.inl i)))) =
          Fin.snoc (z ∘ Sum.inl ∘ Sum.inl) (y 0) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [σ]
      · simp [σ]
    change (∃ y : Fin 1 → M,
      (z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
        y 0 = f (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))) ∧
      z ∘ Sum.inr = FullBaseFiniteCodes.code d F
        (fun i => Sum.elim z y (σ (.inl (.inl i)))) (z (.inl (.inr 0)))) ↔ _
    simp only [hparam]
    constructor
    · rintro ⟨y,⟨hx,hy⟩,he⟩
      exact ⟨hx,by simpa only [hy] using he⟩
    · rintro ⟨hx,he⟩
      exact ⟨![f (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))],⟨hx,rfl⟩,he⟩
  refine ⟨d,e,?_,hE,?_⟩
  · intro p x i hx
    exact FullBaseFiniteCodes.code_sorted d F (Fin.snoc p (f p x)) ⟨x,hx⟩ i
  · intro p x hx y hy hxy he
    let t : Fin (n+1) → M := Fin.snoc p (f p x)
    let X : VFType (M := M) := ⟨x,hAVF p hx⟩
    let Y : VFType (M := M) := ⟨y,hAVF p hy⟩
    have hX : X ∈ F t := (hMem t X).mpr (by
      simp only [t,Fin.init_snoc,Fin.snoc_last]
      exact ⟨hx,rfl⟩)
    have hY : Y ∈ F t := (hMem t Y).mpr (by
      simp only [t,Fin.init_snoc,Fin.snoc_last]
      exact ⟨hy,hxy.symm⟩)
    have he' : FullBaseFiniteCodes.code d F t X.val = FullBaseFiniteCodes.code d F t Y.val := by
      change e p x = FullBaseFiniteCodes.code d F (Fin.snoc p (f p x)) y
      rw [he]
      change FullBaseFiniteCodes.code d F (Fin.snoc p (f p y)) y = _
      rw [hxy]
    exact congrArg Subtype.val (FullBaseFiniteCodes.code_injective h00 d F hBound t hX hY he')

end IntegrationInACVF.Section4.FiniteScalarFamilies
