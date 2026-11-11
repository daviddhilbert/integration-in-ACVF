import IntegrationSection4.Cells
import IntegrationSection4.GammaBaseDescent
import IntegrationSection3ACVF.RVDifferencePairs

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.DefinableParadigms

open Cells BalancedFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem pairCodes_iff (R : Set (VF (M := M) × VF (M := M))) (a b : M) :
    ![a,b] ∈ pairCodes R ↔ ∃ x y : VF (M := M), (x,y) ∈ R ∧ a = x.val ∧ b = y.val := by
  constructor
  · rintro ⟨p,hp,he⟩
    exact ⟨p.1,p.2,hp,congrFun he 0,congrFun he 1⟩
  · rintro ⟨x,y,hxy,ha,hb⟩
    exact ⟨(x,y),hxy,by rw [ha,hb]⟩

theorem positionCodes_iff (D : Set (VF (M := M))) (f : VF (M := M) → VF (M := M)) (a b : M) :
    ![a,b] ∈ positionCodes D f ↔ ∃ x : VF (M := M), x ∈ D ∧ a = x.val ∧ b = (f x).val := by
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨x,hx,congrFun he 0,congrFun he 1⟩
  · rintro ⟨x,hx,ha,hb⟩
    exact ⟨x,hx,by rw [ha,hb]⟩

theorem raw_range_definable (B : FullBaseAtomicity.Base (M := M))
    (R F : Set (Fin 2 → M)) (hR : FullBaseAtomicity.OverBase B R) (hF : FullBaseAtomicity.OverBase B F)
    (r₀ r₁ f₀ f₁ i j : Fin 3) : FullBaseAtomicity.OverBase B
      {u : Fin 1 → M | ∃ w : Fin 3 → M, ![w r₀,w r₁] ∈ R ∧ ![w f₀,w f₁] ∈ F ∧
        u 0 = RVDifferencePairs.difference (w i) (w j)} := by
  let ι := Fin 1 ⊕ Fin 3
  have hr := FullBaseAtomicity.OverBase.preimage_comp hR (![.inr r₀,.inr r₁] : Fin 2 → ι)
  have hf := FullBaseAtomicity.OverBase.preimage_comp hF (![.inr f₀,.inr f₁] : Fin 2 → ι)
  have hd := FullBaseAtomicity.OverBase.preimage_comp (RVDifferencePairs.difference_graph_definable B)
    (![.inr i,.inr j,.inl 0] : Fin 3 → ι)
  have h := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hr
    (FullBaseAtomicity.OverBase.inter hf hd))
  apply FullBaseAtomicity.OverBase.congr h
  intro u
  have ht (w : Fin 3 → M) (a b : Fin 3) : Sum.elim u w ∘ (![.inr a,.inr b] : Fin 2 → ι) = ![w a,w b] := by
    funext k; fin_cases k <;> rfl
  change (∃ w : Fin 3 → M, Sum.elim u w ∘ (![.inr r₀,.inr r₁] : Fin 2 → ι) ∈ R ∧
    Sum.elim u w ∘ (![.inr f₀,.inr f₁] : Fin 2 → ι) ∈ F ∧ u 0 = RVDifferencePairs.difference (w i) (w j)) ↔ _
  simp only [ht]
  rfl

def verticalValues (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M)) : Set M :=
  {u | ∃ p ∈ R, u = (rv (p.2-f p.1)).val}

def horizontalValues (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M)) : Set M :=
  {u | ∃ a x : VF (M := M), x ∈ first R ∧ (a,f x) ∈ R ∧ u = (rv (a-x)).val}

theorem vertical_definable (G : GammaParameters.Base (M := M))
    (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M))
    (hR : DefinableOverBase G (fun _ : Fin 2 => .vf) (pairCodes R))
    (hf : DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes (first R) f)) :
    FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) {z : Fin 1 → M | z 0 ∈ verticalValues R f} := by
  have h := raw_range_definable (GammaBaseBridge.fullBase G) _ _
    (GammaBaseBridge.of_gamma G hR) (GammaBaseBridge.of_gamma G hf) 0 1 0 2 1 2
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  constructor
  · rintro ⟨w,hwR,hwf,he⟩
    obtain ⟨a,b,hab,ha,hb⟩ := (pairCodes_iff R _ _).mp hwR
    obtain ⟨x,hx,hax,hfx⟩ := (positionCodes_iff (first R) f _ _).mp hwf
    have hxa : x = a := Subtype.ext (hax.symm.trans ha)
    subst x
    rw [hb,hfx,RVDifferencePairs.difference_vf b (f a)] at he
    exact ⟨(a,b),hab,he⟩
  · rintro ⟨p,hp,he⟩
    refine ⟨![p.1.val,p.2.val,(f p.1).val],⟨p,hp,rfl⟩,
      ⟨p.1,⟨p,hp,rfl⟩,rfl⟩,?_⟩
    change z 0 = RVDifferencePairs.difference p.2.val (f p.1).val
    rw [RVDifferencePairs.difference_vf p.2 (f p.1)]
    exact he

theorem horizontal_definable (G : GammaParameters.Base (M := M))
    (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M))
    (hR : DefinableOverBase G (fun _ : Fin 2 => .vf) (pairCodes R))
    (hf : DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes (first R) f)) :
    FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) {z : Fin 1 → M | z 0 ∈ horizontalValues R f} := by
  have h := raw_range_definable (GammaBaseBridge.fullBase G) _ _
    (GammaBaseBridge.of_gamma G hR) (GammaBaseBridge.of_gamma G hf) 0 2 1 2 0 1
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  constructor
  · rintro ⟨w,hwR,hwf,he⟩
    obtain ⟨a,b,hab,ha,hb⟩ := (pairCodes_iff R _ _).mp hwR
    obtain ⟨x,hx,hax,hfx⟩ := (positionCodes_iff (first R) f _ _).mp hwf
    have hbf : b = f x := Subtype.ext (hb.symm.trans hfx)
    rw [ha,hax,RVDifferencePairs.difference_vf a x] at he
    exact ⟨a,x,hx,hbf ▸ hab,he⟩
  · rintro ⟨a,x,hx,hax,he⟩
    refine ⟨![a.val,x.val,(f x).val],⟨(a,f x),hax,rfl⟩,⟨x,hx,rfl⟩,?_⟩
    change z 0 = RVDifferencePairs.difference a.val x.val
    rw [RVDifferencePairs.difference_vf a x]
    exact he

theorem singleton_of_full (G : GammaParameters.Base (M := M)) (t : RV (M := M))
    (h : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) {z : Fin 1 → M | z 0 ∈ ({t.val} : Set M)}) :
    DefinableAtBase G .rv {t.val} := by
  apply GammaBaseDescent.to_gamma G _ _ h
  intro z hz i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hz.symm ▸ t.property

theorem vertical_singleton {R : Set (VF (M := M) × VF (M := M))}
    {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}
    (h : CellData R f t) (hne : R.Nonempty) : verticalValues R f = {t.val} := by
  have hv (p : VF (M := M) × VF (M := M)) (hp : p ∈ R) : rv (p.2-f p.1) = t := by
    have ha : p.1 ∈ first R := ⟨p,hp,rfl⟩
    have hh : p.2 ∈ fibre R p.1 := hp
    rw [h.fibres p.1 ha] at hh
    exact hh
  ext u
  constructor
  · rintro ⟨p,hp,hu⟩
    exact hu.trans (congrArg Subtype.val (hv p hp))
  · intro hu
    obtain ⟨p,hp⟩ := hne
    exact ⟨p,hp,hu.trans (congrArg Subtype.val (hv p hp)).symm⟩

theorem horizontal_singleton {R : Set (VF (M := M) × VF (M := M))}
    {f : VF (M := M) → VF (M := M)} {t₁ t₂ : RV (M := M)}
    (h : HasBalancedFibres (first R) (second R) R f t₁ t₂) (hne : R.Nonempty) :
    horizontalValues R f = {t₁.val} := by
  have hv (a x : VF (M := M)) (hx : x ∈ first R) (hax : (a,f x) ∈ R) : rv (a-x) = t₁ := by
    have ha := (h.subset hax).1
    exact (Set.ext_iff.mp (h.horizontal a ha) x).mp ⟨hx,hax⟩
  ext u
  constructor
  · rintro ⟨a,x,hx,hax,hu⟩
    exact hu.trans (congrArg Subtype.val (hv a x hx hax))
  · intro hu
    obtain ⟨p,hp⟩ := hne
    obtain ⟨x,hx,hfx⟩ := h.bijective.2.2 (show p.2 ∈ second R from ⟨p,hp,rfl⟩)
    have hax : (p.1,f x) ∈ R := hfx.symm ▸ hp
    exact ⟨p.1,x,hx,hax,hu.trans (congrArg Subtype.val (hv p.1 x hx hax)).symm⟩

/-- Full graph definability makes every paradigm in a nonempty cell
definable. This also covers every possible balanced first paradigm. -/
theorem cellData (G : GammaParameters.Base (M := M))
    (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M)) (t : RV (M := M))
    (h : CellData R f t) (hne : R.Nonempty)
    (hR : DefinableOverBase G (fun _ : Fin 2 => .vf) (pairCodes R))
    (hf : DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes (first R) f)) :
    DefinableCellData G R f t := by
  have hv := vertical_definable G R f hR hf
  rw [vertical_singleton h hne] at hv
  refine ⟨h,hR,hf,singleton_of_full G t hv,?_⟩
  intro t₁ hBal
  have hh := horizontal_definable G R f hR hf
  rw [horizontal_singleton hBal.2.2.1 hne] at hh
  exact singleton_of_full G t₁ hh

end IntegrationInACVF.Section4.DefinableParadigms
