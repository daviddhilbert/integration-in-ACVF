import IntegrationSection3ACVF.GammaLinearRadiusClosure
import IntegrationSection3ACVF.FullGammaBounds

/-! Existence of a least actual linear radius once the ordinary-radius
locus has its full first-order definition and a lower bound. The empty
ordinary locus gives the singleton radius infinity. Definability remains
an explicit bridge obligation in this helper. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.LeastLinearRadiusGeometry

open LinearRadiusThreshold GammaRadiusAtomicity GammaLinearRestrictions GammaLinearRadiusClosure

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_mem_iff (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (c : VFType (M := M)) (γ : Values.Gamma (M := M)) :
    γ ∈ locus A f hfVF c ↔ LinearOnRadius A f hfVF c γ.val := by
  constructor
  · rintro ⟨s,hSub,hLin⟩
    have hSub' : ballAt c γ.val ⊆ A := (ballAt_gamma c γ).symm ▸ hSub
    refine ⟨hSub',s,?_⟩
    intro x y hx hy
    exact hLin x y ((ballAt_gamma c γ) ▸ hx) ((ballAt_gamma c γ) ▸ hy)
  · rintro ⟨hSub,s,hLin⟩
    have hSub' : gammaBall c γ true ⊆ A := (ballAt_gamma c γ) ▸ hSub
    refine ⟨s,hSub',?_⟩
    intro x y hx hy
    exact hLin x y ((ballAt_gamma c γ).symm ▸ hx) ((ballAt_gamma c γ).symm ▸ hy)

theorem singleton_linear (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (c : VFType (M := M)) (hc : c.val ∈ A) : LinearOnRadius A f hfVF c Values.infinity := by
  have hSub : ballAt c Values.infinity ⊆ A := by
    rw [ballAt_infinity]
    intro z hz
    exact hz ▸ hc
  refine ⟨hSub,1,?_⟩
  intro x y hx hy
  have hxC : x = c := Subtype.ext (by
    have h := hx
    rw [ballAt_infinity c] at h
    exact h)
  have hyC : y = c := Subtype.ext (by
    have h := hy
    rw [ballAt_infinity c] at h
    exact h)
  subst x
  subst y
  let fc : VFType (M := M) := ⟨f c.val,hfVF _ hc⟩
  change Values.vfValueHom (fc-fc) = (1 : Values.Gamma (M := M)).val * Values.vfValueHom (c-c)
  simp only [sub_self,map_zero,mul_zero]

theorem exists_least_of_definable (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x)) (c : VFType (M := M)) (hc : c.val ∈ A)
    (hDef : FullGammaSyntax.Scalar B (locus A f hfVF c)) (hBound : BddBelow (locus A f hfVF c)) :
    ∃ r : Values.GammaTop (M := M), IsLeastLinearRadius A f hfVF c r := by
  by_cases hNonempty : (locus A f hfVF c).Nonempty
  · obtain ⟨γ,hγ⟩ := FullGammaBounds.exists_isLeast_of_closed_upper h00 B hDef hNonempty hBound
      (fun ρ hρ τ hρτ => upward A f hfVF c ρ τ hρ hρτ) (closed_above A f hfVF c)
    refine ⟨γ.val,(gamma_mem_iff A f hfVF c γ).mp hγ.1,?_⟩
    intro r hr
    by_cases hInf : r = Values.infinity
    · rw [hInf]
      exact Values.le_infinity _
    · let τ : Values.Gamma (M := M) := ⟨r,hInf⟩
      exact hγ.2 ((gamma_mem_iff A f hfVF c τ).mpr hr)
  · refine ⟨Values.infinity,singleton_linear A f hfVF c hc,?_⟩
    intro r hr
    by_cases hInf : r = Values.infinity
    · exact hInf.symm.le
    · let τ : Values.Gamma (M := M) := ⟨r,hInf⟩
      exact (hNonempty ⟨τ,(gamma_mem_iff A f hfVF c τ).mpr hr⟩).elim

theorem ordinary_locus_bounded (a c : VFType (M := M)) (α : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) :
    BddBelow (locus (gammaBall a α true) f hfVF c) := by
  obtain ⟨δ,hδ⟩ := exists_gt (1 : Values.Gamma (M := M))
  refine ⟨α,?_⟩
  rintro τ ⟨s,hSub,_⟩
  exact BallEnlargementGeometry.gamma_radius_le_of_subset δ hδ c a α τ true true hSub

end IntegrationInACVF.Section3ACVF.LeastLinearRadiusGeometry
