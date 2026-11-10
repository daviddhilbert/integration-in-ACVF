import IntegrationSection3ACVF.LinearSubballSpecialization

/-! Corollary 3.17 with the paper's least-radius predicate. Infinity
means the singleton at the centre; VF has its separate bottom radius. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.LinearRadiusThreshold

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def ballAt (x : VFType (M := M)) (r : Values.GammaTop (M := M)) : Set M :=
  if h : r = Values.infinity then {x.val} else gammaBall x ⟨r,h⟩ true

theorem ballAt_gamma (x : VFType (M := M)) (γ : Values.Gamma (M := M)) :
    ballAt x γ.val = gammaBall x γ true := by
  simp only [ballAt,dite_eq_right γ.property]
  rfl

theorem ballAt_infinity (x : VFType (M := M)) :
    ballAt x Values.infinity = {x.val} := by
  simp only [ballAt,dite_true]

def LinearOnRadius (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (x : VFType (M := M)) (r : Values.GammaTop (M := M)) : Prop :=
  ∃ hsub : ballAt x r ⊆ A, ∃ s : Values.Gamma (M := M),
    GammaLinearity.GammaLinear (ballAt x r) f (fun y hy => hfVF y (hsub hy)) s

def IsLeastLinearRadius (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (x : VFType (M := M)) (r : Values.GammaTop (M := M)) : Prop :=
  IsLeast {t | LinearOnRadius A f hfVF x t} r

theorem exists_at_radius {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    {A : Set M} (ho : PaperBalls.IsOpenBall A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (ρ : PaperBalls.Radius (M := M)) (hRad : PaperBalls.HasRadius A ρ)
    (β : Values.Gamma (M := M)) (hρβ : ρ < (↑β.val : PaperBalls.Radius (M := M))) :
    ∃ c : VFType (M := M), c.val ∈ A ∧ LinearOnRadius A f hfVF c β.val := by
  have hFound : ∃ c : VFType (M := M), c.val ∈ A ∧
      ∃ hsub : gammaBall c β true ⊆ A, ∃ s : Values.Gamma (M := M),
        GammaLinearity.GammaLinear (gammaBall c β true) f (fun x hx => hfVF x (hsub hx)) s := by
    rcases ho with hAll | ⟨a,α,hA⟩
    · obtain ⟨α,hαβ⟩ := exists_lt β
      have hsub : gammaBall (0 : VFType (M := M)) α true ⊆ A := by
        intro x hx
        rw [hAll]
        exact hx.1
      exact LinearSubballSpecialization.inside_open_ball hκ hs B hsmall h00 f hf hfVF hinj 0 α β hαβ hsub
    · obtain ⟨δ,hδ1⟩ := exists_gt (1 : Values.Gamma (M := M))
      have hRadα : PaperBalls.HasRadius A (↑α.val : PaperBalls.Radius (M := M)) :=
        Or.inr (Or.inr ⟨a,α,true,hA,rfl⟩)
      have he := PaperBallInvariants.hasRadius_unique δ hδ1 hRad hRadα
      have hαβ : α < β := by
        rw [he] at hρβ
        have h : α.val < β.val := WithBot.coe_lt_coe.mp hρβ
        exact h
      exact LinearSubballSpecialization.inside_open_ball hκ hs B hsmall h00 f hf hfVF hinj a α β hαβ
        (hA.symm ▸ Set.Subset.rfl)
  obtain ⟨c,hc,hsub,s,hLin⟩ := hFound
  refine ⟨c,hc,?_⟩
  have he := ballAt_gamma c β
  have hsub' : ballAt c β.val ⊆ A := he.symm ▸ hsub
  refine ⟨hsub',s,?_⟩
  intro x y hx hy
  exact hLin x y ((Set.ext_iff.mp he _).mp hx) ((Set.ext_iff.mp he _).mp hy)

theorem corollary_3_17 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    {A : Set M} (ho : PaperBalls.IsOpenBall A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (ρ : PaperBalls.Radius (M := M)) (hRad : PaperBalls.HasRadius A ρ)
    (threshold : VFType (M := M) → Values.GammaTop (M := M))
    (hLeast : ∀ x : VFType (M := M), x.val ∈ A → IsLeastLinearRadius A f hfVF x (threshold x)) :
    ¬ ∃ β : Values.Gamma (M := M), ρ < (↑β.val : PaperBalls.Radius (M := M)) ∧
      ∀ x : VFType (M := M), x.val ∈ A → β.val < threshold x := by
  rintro ⟨β,hρβ,hAll⟩
  obtain ⟨c,hc,hLin⟩ := exists_at_radius hκ hs B hsmall h00 ho f hf hfVF hinj ρ hRad β hρβ
  exact not_lt_of_ge ((hLeast c hc).2 hLin) (hAll c hc)

end IntegrationInACVF.Section3ACVF.LinearRadiusThreshold
