import IntegrationSection3ACVF.FullRVValueFibres
import IntegrationSection3ACVF.RVFunctionValueCuts
import IntegrationSection3.CofiniteFunctionFibres

/-! A definable map on one entire actual RV value fibre has one dominant
output value. Injectivity makes the corresponding image cofinite in that
entire target value fibre. All graph and cofinite premises are constructed. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.CofiniteRVRows

open FullRVValueFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def row (g : M → M) (γ η : Values.Gamma (M := M)) : Set M :=
  {x | x ∈ fibre γ ∧ codeValue (g x) = η}

theorem row_definable (B : FullBaseAtomicity.Base (M := M)) (g : M → M)
    (γ η : Values.Gamma (M := M))
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (fibre γ) g))
    (hOut : ∀ x ∈ fibre γ, NonzeroRV (g x)) :
    FullBaseAtomicity.OverBase (B.adjoin (Sum.inr η)) {z : Fin 1 → M | z 0 ∈ row g γ η} := by
  let C := B.adjoin (Sum.inr η)
  have hGC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (fibre γ) g) :=
    FullBaseAtomicity.OverBase.mono hG Set.Subset.rfl (Set.subset_insert _ _)
  have hη : FullBaseAtomicity.OverBase C {z : Fin 1 → M | z 0 ∈ fibre η} :=
    AdjoinGamma.named_scalar η (Set.mem_insert _ _)
  have hp := ParameterPresentation.codeDomain_definable (M := M) C.real
  have hPre : FullBaseAtomicity.OverBase C {z : Fin 1 → M | z 0 ∈ fibre γ ∧ g (z 0) ∈ fibre η} := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryBaseImages.preimage_definable hp hGC hη
  apply FullBaseAtomicity.OverBase.congr hPre
  intro z
  change (z 0 ∈ fibre γ ∧ g (z 0) ∈ fibre η) ↔ (z 0 ∈ fibre γ ∧ codeValue (g (z 0)) = η)
  exact and_congr_right (fun hx => mem_fibre_code η (g (z 0)) (hOut _ hx))

theorem exists_unique_dominant {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (g : M → M) (γ : Values.Gamma (M := M))
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (fibre γ) g))
    (hOut : ∀ x ∈ fibre γ, NonzeroRV (g x)) :
    ∃! η : Values.Gamma (M := M), (fibre γ \ row g γ η).Finite := by
  have hImage := RVFunctionValueCuts.finite_value_image hκ hs B hsmall (fibre γ) g hG
    (fun t ht => (subset_nonzero γ ht).1) hOut γ (fun t ht => (mem_fibre γ t).mp ht)
  have hSide (η : Values.Gamma (M := M)) : (row g γ η).Finite ∨ (fibre γ \ row g γ η).Finite := by
    have h := finite_or_cofinite (B.adjoin (Sum.inr η)) (row g γ η) (row_definable B g γ η hG hOut)
      (fun t ht => (subset_nonzero γ ht.1).1) γ
    have he : row g γ η ∩ fibre γ = row g γ η := Set.inter_eq_left.mpr (fun _ ht => ht.1)
    rwa [he] at h
  exact CofiniteFunctionFibres.exists_unique_cofinite_fibre (fibre γ) (fun x => codeValue (g x))
    (fibre_infinite h00 γ) hImage hSide

theorem cofinite_target (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (g : M → M) (γ η : Values.Gamma (M := M))
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (fibre γ) g))
    (hOut : ∀ x ∈ fibre γ, NonzeroRV (g x)) (hInj : Set.InjOn g (fibre γ))
    (hCo : (fibre γ \ row g γ η).Finite) : (fibre η \ g '' fibre γ).Finite := by
  let C := B.adjoin (Sum.inr η)
  let R := row g γ η
  have hR : FullBaseAtomicity.OverBase C {z : Fin 1 → M | z 0 ∈ R} := row_definable B g γ η hG hOut
  have hGC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (fibre γ) g) :=
    FullBaseAtomicity.OverBase.mono hG Set.Subset.rfl (Set.subset_insert _ _)
  have hRG : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn R g) := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hGC
      (FullBaseAtomicity.OverBase.preimage_comp hR (fun _ => (0 : Fin 2))))
    intro z
    change ((z 0 ∈ fibre γ ∧ z 1 = g (z 0)) ∧ z 0 ∈ R) ↔ (z 0 ∈ R ∧ z 1 = g (z 0))
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.1,h.2⟩,h.1⟩⟩
  have hImg : FullBaseAtomicity.OverBase C {z : Fin 1 → M | z 0 ∈ g '' R} := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryBaseImages.image_definable hRG
  have hSub : g '' R ⊆ fibre η := by
    rintro y ⟨x,hx,rfl⟩
    exact (mem_fibre_code η (g x) (hOut _ hx.1)).mpr hx.2
  have hRInf : R.Infinite := by
    have h := (fibre_infinite h00 γ).sdiff hCo
    apply h.mono
    intro x hx
    by_contra hn
    exact hx.2 ⟨hx.1,hn⟩
  have hImgInf : (g '' R).Infinite := hRInf.image (hInj.mono (fun _ hx => hx.1))
  have hSide := finite_or_cofinite C (g '' R) hImg (fun y hy => (subset_nonzero η (hSub hy)).1) η
  have he : (g '' R) ∩ fibre η = g '' R := Set.inter_eq_left.mpr hSub
  rw [he] at hSide
  have hCoImg : (fibre η \ g '' R).Finite := hSide.resolve_left (fun h => hImgInf h)
  exact hCoImg.subset (fun _ hx => ⟨hx.1,fun hy => hx.2 (Set.image_mono (fun _ hz => hz.1) hy)⟩)

end IntegrationInACVF.Section3ACVF.CofiniteRVRows
