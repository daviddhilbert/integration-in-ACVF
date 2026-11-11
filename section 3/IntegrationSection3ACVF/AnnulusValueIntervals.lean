import IntegrationSection3ACVF.BallEnlargementGeometry

/-! Exact value intervals of actual concentric punctured balls. The
closed parent gives a closed interval, the ordinary open parent a half-open
interval, and VF as open parent a closed ray. The hole is an ordinary open ball. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AnnulusValueIntervals

open GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def valueImage (a : VFType (M := M)) (D : Set M) : Set (Values.GammaTop (M := M)) :=
  (fun x : VFType (M := M) => Values.vfValueHom (x-a)) '' {x | x.val ∈ D}

theorem mem_closed (a x : VFType (M := M)) (ρ : Values.Gamma (M := M)) :
    x.val ∈ gammaBall a ρ false ↔ ρ.val ≤ Values.vfValueHom (x-a) := by
  constructor
  · rintro ⟨_,h,_⟩
    exact h
  · intro h
    exact ⟨x.property,h,by intro he; cases he⟩

theorem mem_open (a x : VFType (M := M)) (ρ : Values.Gamma (M := M)) :
    x.val ∈ gammaBall a ρ true ↔ ρ.val < Values.vfValueHom (x-a) := by
  constructor
  · rintro ⟨_,_,h⟩
    exact lt_of_not_ge (h rfl)
  · intro h
    exact ⟨x.property,h.le,fun _ => not_le_of_gt h⟩

theorem value_representative_below (a : VFType (M := M)) (τ : Values.Gamma (M := M))
    (γ : Values.GammaTop (M := M)) (hγ : γ ≤ τ.val) :
    ∃ x : VFType (M := M), Values.vfValueHom (x-a) = γ := by
  have hFinite : γ ≠ Values.infinity := by
    intro he
    have hτ : τ.val = Values.infinity := le_antisymm (Values.le_infinity τ.val) (he ▸ hγ)
    exact τ.property hτ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative (⟨γ,hFinite⟩ : Values.Gamma (M := M))
  refine ⟨a+r,?_⟩
  simpa only [add_sub_cancel_left] using hr

theorem closed_image (a : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) :
    valueImage a (gammaBall a ρ false \ gammaBall a τ true) = Set.Icc ρ.val τ.val := by
  ext γ
  constructor
  · rintro ⟨x,⟨hx,hHole⟩,rfl⟩
    exact ⟨(mem_closed a x ρ).mp hx,le_of_not_gt (fun h => hHole ((mem_open a x τ).mpr h))⟩
  · rintro ⟨hρ,hτ⟩
    obtain ⟨x,hx⟩ := value_representative_below a τ γ hτ
    refine ⟨x,⟨?_,?_⟩,hx⟩
    · exact (mem_closed a x ρ).mpr (hx.symm ▸ hρ)
    · intro hh
      have h := (mem_open a x τ).mp hh
      rw [hx] at h
      exact (not_lt_of_ge hτ) h

theorem open_image (a : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) :
    valueImage a (gammaBall a ρ true \ gammaBall a τ true) = Set.Ioc ρ.val τ.val := by
  ext γ
  constructor
  · rintro ⟨x,⟨hx,hHole⟩,rfl⟩
    exact ⟨(mem_open a x ρ).mp hx,le_of_not_gt (fun h => hHole ((mem_open a x τ).mpr h))⟩
  · rintro ⟨hρ,hτ⟩
    obtain ⟨x,hx⟩ := value_representative_below a τ γ hτ
    refine ⟨x,⟨?_,?_⟩,hx⟩
    · exact (mem_open a x ρ).mpr (hx.symm ▸ hρ)
    · intro hh
      have h := (mem_open a x τ).mp hh
      rw [hx] at h
      exact (not_lt_of_ge hτ) h

theorem whole_field_image (a : VFType (M := M)) (τ : Values.Gamma (M := M)) :
    valueImage a ({x | iVF x} \ gammaBall a τ true) = Set.Iic τ.val := by
  ext γ
  constructor
  · rintro ⟨x,⟨_,hHole⟩,rfl⟩
    exact le_of_not_gt (fun h => hHole ((mem_open a x τ).mpr h))
  · intro hτ
    obtain ⟨x,hx⟩ := value_representative_below a τ γ hτ
    refine ⟨x,⟨x.property,?_⟩,hx⟩
    intro hh
    have h := (mem_open a x τ).mp hh
    rw [hx] at h
    exact (not_lt_of_ge hτ) h

end IntegrationInACVF.Section3ACVF.AnnulusValueIntervals
