import IntegrationSection4.FullBaseFiniteCodes
import IntegrationSection4.FullBaseFiniteBounds
import IntegrationSection4.GammaTupleGraphs

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaFiniteFibreRefinement

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A finite-to-one scalar VF map is refined to an injection by finitely
many RV coordinates, definably over its original Gamma base. -/
theorem exists_refinement {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (A : Set M) (hAVF : A ⊆ {x | iVF x}) (f : M → M)
    (hf : DefinableOverBase G (fun _ : Fin 2 => .vf) (ImaginaryBaseImages.graphOn A f))
    (hFin : ∀ y, {x | x ∈ A ∧ f x = y}.Finite) :
    ∃ d : ℕ, ∃ e : M → Fin d → M,
      (∀ x ∈ A, ∀ i, iRV (e x i)) ∧
      GammaGraphDefinable G (fun (p : Point (M := M) 1 0) (q : Point (M := M) 0 d) =>
        (vfAt p 0).val ∈ A ∧ (fun i => (q.2 i).val) = e (vfAt p 0).val) ∧
      ∀ x ∈ A, ∀ y ∈ A, f x = f y → e x = e y → x = y := by
  let B := GammaBaseBridge.fullBase G
  have hfB := GammaBaseBridge.of_gamma G hf
  have hPre (t : Fin 1 → M) : {x : VFType (M := M) | x.val ∈ A ∧ f x.val = t 0}.Finite :=
    (hFin (t 0)).preimage Subtype.val_injective.injOn
  let F (t : Fin 1 → M) : Finset (VFType (M := M)) := (hPre t).toFinset
  have hMem (t : Fin 1 → M) (x : VFType (M := M)) : x ∈ F t ↔ x.val ∈ A ∧ f x.val = t 0 :=
    (hPre t).mem_toFinset
  have hF : FullBaseAtomicity.OverBase B {z : Fin 1 ⊕ Fin 1 → M |
      ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)} := by
    have hh := FullBaseAtomicity.OverBase.preimage_comp hfB (![.inr 0,.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1)
    apply FullBaseAtomicity.OverBase.congr hh
    intro z
    change (z (.inr 0) ∈ A ∧ z (.inl 0) = f (z (.inr 0))) ↔ _
    constructor
    · intro h
      exact ⟨⟨z (.inr 0),hAVF h.1⟩,(hMem _ _).mpr ⟨h.1,h.2.symm⟩,rfl⟩
    · rintro ⟨x,hx,he⟩
      have hh := (hMem _ _).mp hx
      rw [he] at hh
      exact ⟨hh.1,hh.2.symm⟩
  obtain ⟨d,hBound⟩ := FullBaseFiniteBounds.uniform_bound hκ hs B hsmall F hF
  let e : M → Fin d → M := fun x => FullBaseFiniteCodes.code d F ![f x] x
  have hSort (x : M) (hx : x ∈ A) (i : Fin d) : iRV (e x i) :=
    FullBaseFiniteCodes.code_sorted d F ![f x] ⟨x,hAVF hx⟩ i
  have hCode := FullBaseFunctions.tuple_graph B (fun i : Fin d =>
    FullBaseFiniteCodes.code_graph B h00 d F hF d hBound i)
  let ι := (Fin 1 ⊕ Fin d) ⊕ Fin 1
  have hFun := FullBaseAtomicity.OverBase.preimage_comp hfB
    (![.inl (.inl 0),.inr 0] : Fin 2 → ι)
  let π : (Fin 1 ⊕ Fin 1) ⊕ Fin d → ι :=
    Sum.elim (Sum.elim (fun _ => .inr 0) (fun _ => .inl (.inl 0))) (fun i => .inl (.inr i))
  have hCode' := FullBaseAtomicity.OverBase.preimage_comp hCode π
  have hE : FullBaseAtomicity.OverBase B {z : Fin 1 ⊕ Fin d → M |
      z (.inl 0) ∈ A ∧ z ∘ Sum.inr = e (z (.inl 0))} := by
    have hh := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hFun hCode')
    apply FullBaseAtomicity.OverBase.congr hh
    intro z
    have ht (y : Fin 1 → M) : (fun _ : Fin 1 => y 0) = y := by funext i; fin_cases i; rfl
    change (∃ y : Fin 1 → M, (z (.inl 0) ∈ A ∧ y 0 = f (z (.inl 0))) ∧
      z ∘ Sum.inr = FullBaseFiniteCodes.code d F (fun _ => y 0) (z (.inl 0))) ↔ _
    constructor
    · rintro ⟨y,⟨hx,hy⟩,he⟩
      have hy' : (fun _ : Fin 1 => y 0) = ![f (z (.inl 0))] := by funext i; fin_cases i; exact hy
      exact ⟨hx,by rwa [hy'] at he⟩
    · rintro ⟨hx,he⟩
      refine ⟨![f (z (.inl 0))],⟨hx,rfl⟩,?_⟩
      have heta : (fun _ : Fin 1 => ![f (z (.inl 0))] 0) = ![f (z (.inl 0))] := by
        funext i; fin_cases i; rfl
      rw [heta]
      exact he
  let R : Set (Fin ((1+0)+(0+d)) → M) := {z | z 0 ∈ A ∧
    (fun i : Fin d => z (Fin.natAdd (1+0) (Fin.natAdd 0 i))) = e (z 0)}
  have hR : FullBaseAtomicity.OverBase B R := by
    exact FullBaseAtomicity.OverBase.preimage_comp hE
      (Sum.elim (fun _ : Fin 1 => (0 : Fin ((1+0)+(0+d))))
        (fun i => Fin.natAdd (1+0) (Fin.natAdd 0 i)))
  have hProper : ∀ z ∈ R, ∀ i,
      sortEval (Fin.append (gammaPointSort 1 0) (gammaPointSort 0 d) i) (z i) := by
    intro z hz i
    cases i using Fin.addCases with
    | left i => fin_cases i; exact hAVF hz.1
    | right i =>
      cases i using Fin.addCases with
      | left i => exact i.elim0
      | right i =>
        have hh := congrFun hz.2 i
        rw [hh]
        simpa only [Fin.append_right,gammaPointSort,sortEval,iRV] using hSort _ hz.1 i
  have hΓ := GammaTupleGraphs.of_full G R hR hProper
  refine ⟨d,e,hSort,?_,?_⟩
  · apply GammaGraphDefinable.congr hΓ
    intro p q
    change ((vfAt p 0).val ∈ A ∧
      (fun i : Fin d => Fin.append (gammaPointCode p) (gammaPointCode q)
        (Fin.natAdd (1+0) (Fin.natAdd 0 i))) = e (vfAt p 0).val) ↔ _
    simp only [Fin.append_right,gammaPointCode,Fin.append_right]
  · intro x hx y hy hxy he
    let X : VFType (M := M) := ⟨x,hAVF hx⟩
    let Y : VFType (M := M) := ⟨y,hAVF hy⟩
    have hX : X ∈ F ![f x] := (hMem _ _).mpr ⟨hx,rfl⟩
    have hY : Y ∈ F ![f x] := (hMem _ _).mpr ⟨hy,hxy.symm⟩
    have he' : FullBaseFiniteCodes.code d F ![f x] X.val = FullBaseFiniteCodes.code d F ![f x] Y.val := by
      change e x = FullBaseFiniteCodes.code d F ![f x] y
      rw [he]
      change FullBaseFiniteCodes.code d F ![f y] y = FullBaseFiniteCodes.code d F ![f x] y
      rw [hxy]
    exact congrArg Subtype.val (FullBaseFiniteCodes.code_injective h00 d F hBound ![f x] hX hY he')

end IntegrationInACVF.Section4.GammaFiniteFibreRefinement
