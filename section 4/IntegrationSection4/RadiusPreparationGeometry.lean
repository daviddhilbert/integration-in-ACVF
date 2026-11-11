import IntegrationSection3ACVF.AffineHoleGeometry
import IntegrationSection4.RadiusBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open GammaRadiusAtomicity

namespace IntegrationInACVF.Section4.RadiusPreparationGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem recentre (a x : VFType (M := M)) (γ : Values.Gamma (M := M))
    (hx : x.val ∈ gammaBall a γ true) : gammaBall x γ true = gammaBall a γ true := by
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have hax := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr x).mp hx
  have ht (u w z : VFType (M := M)) : v (u-z) ≤ max (v (u-w)) (v (w-z)) := by
    calc
      v (u-z) = v ((u-w)+(w-z)) := congrArg v (by ring)
      _ ≤ max (v (u-w)) (v (w-z)) := v.map_add _ _
  ext y
  constructor
  · intro hy
    let Y : VFType (M := M) := ⟨y,hy.1⟩
    have hh := (GammaCosetGeometry.gammaBall_mem_valuation v hv x r γ hr Y).mp hy
    exact (GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr Y).mpr
      (lt_of_le_of_lt (ht Y x a) (max_lt hh hax))
  · intro hy
    let Y : VFType (M := M) := ⟨y,hy.1⟩
    have hh := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr Y).mp hy
    have hxa : v (a-x) < v r := by rwa [v.map_sub_swap a x]
    exact (GammaCosetGeometry.gammaBall_mem_valuation v hv x r γ hr Y).mpr
      (lt_of_le_of_lt (ht Y a x) (max_lt hh hxa))

theorem equal_of_meet (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {D E : Set M} (hD : PaperBalls.IsOpenBall D) (hE : PaperBalls.IsOpenBall E)
    (α : Values.Gamma (M := M))
    (hDr : PaperBalls.HasRadius D (↑α.val : PaperBalls.Radius (M := M)))
    (hEr : PaperBalls.HasRadius E (↑α.val : PaperBalls.Radius (M := M)))
    (x : M) (hxD : x ∈ D) (hxE : x ∈ E) : D = E := by
  obtain ⟨a,rfl⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ hD α hDr
  obtain ⟨b,rfl⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ hE α hEr
  let X : VFType (M := M) := ⟨x,hxD.1⟩
  exact (recentre a X α hxD).symm.trans (recentre b X α hxE)

theorem image_injective {A D E : Set M} (f : M → M) (hf : Set.InjOn f A)
    (hD : D ⊆ A) (hE : E ⊆ A) (he : f '' D = f '' E) : D = E := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,hyx⟩ := he ▸ (show f x ∈ f '' D from ⟨x,hx,rfl⟩)
    exact hf (hE hy) (hD hx) hyx ▸ hy
  · intro hx
    obtain ⟨y,hy,hyx⟩ := he.symm ▸ (show f x ∈ f '' E from ⟨x,hx,rfl⟩)
    exact hf (hD hy) (hE hx) hyx ▸ hy

theorem open_nonempty {D : Set M} (hD : PaperBalls.IsOpenBall D) : D.Nonempty := by
  rcases hD with rfl | ⟨a,γ,rfl⟩
  · exact ⟨(0 : VFType (M := M)).val,(0 : VFType (M := M)).property⟩
  · exact ⟨a.val,BallEnlargementGeometry.gammaBall_centre_mem a γ true⟩

end IntegrationInACVF.Section4.RadiusPreparationGeometry
