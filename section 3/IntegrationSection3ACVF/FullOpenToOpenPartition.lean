import IntegrationSection3ACVF.FiniteBaseOpenImageCovers
import IntegrationSection3ACVF.OpenToOpenPartitions
import IntegrationSection3ACVF.RVInverse

/-! Proposition3.19 over the full original interpreted base. All
compactness code choices are internal; the resulting actual finite
disjoint partition is definable over the original base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullOpenToOpenPartition

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem proposition_3_19_finite_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary.Finite)
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A C : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAVF : A ⊆ {x | iVF x}) (hCVF : C ⊆ {x | iVF x})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A C) :
    ∃ P : Finset (Set M),
      (∀ U ∈ P, U.Nonempty ∧ U ⊆ A ∧
        FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
        MaximalOpenClasses.OpenToOpen U f) ∧
      (P : Set (Set M)).Pairwise Disjoint ∧ A = {x | ∃ U ∈ P, x ∈ U} := by
  classical
  have hImage : f '' A = C := hbij.image_eq
  let g := RVInverse.inverse A f
  have hg : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn C g) := by
    have h := RVInverse.inverse_graph_definable B hbij.2.1 hf
    rwa [hImage] at h
  have hC : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ C} := by
    have h : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ f '' A} := by
      letI := @CanonicalStructure.normalize M sM
      exact ImaginaryBaseImages.image_definable hf
    rwa [hImage] at h
  have hgVF (y : M) (hy : y ∈ C) : iVF (g y) :=
    hAVF (RVInverse.inverse_right ((Set.ext_iff.mp hImage y).mpr hy)).1
  have hgInj : Set.InjOn g C := hImage ▸ RVInverse.inverse_injOn A f
  obtain ⟨F,hF,hCovF⟩ := FiniteBaseOpenImageCovers.finite_cover hκ hs B hB hsmall h00 δ hδ hδ1 hA
    f hf (fun x hx => hCVF (hbij.1 hx)) hbij.2.1
  obtain ⟨G,hG,hCovG⟩ := FiniteBaseOpenImageCovers.finite_cover hκ hs B hB hsmall h00 δ hδ hδ1 hC
    g hg hgVF hgInj
  let H := F.biUnion (fun U => G.image (fun V => U ∩ f ⁻¹' V))
  have hMem (W : Set M) : W ∈ H ↔ ∃ U ∈ F, ∃ V ∈ G, U ∩ f ⁻¹' V = W := by
    simp only [H,Finset.mem_biUnion,Finset.mem_image]
  have hH (W : Set M) (hW : W ∈ H) : W ⊆ A ∧
      FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ W} ∧
      MaximalOpenClasses.OpenToOpen W f := by
    obtain ⟨U,hU,V,hV,rfl⟩ := (hMem W).mp hW
    obtain ⟨hUA,hUdef,hUOpen⟩ := hF U hU
    obtain ⟨hVC,hVdef,hVOpen⟩ := hG V hV
    have hWA : U ∩ f ⁻¹' V ⊆ A := fun x hx => hUA hx.1
    have hPre : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A ∧ f (z 0) ∈ V} := by
      let p := @ParameterPresentation.presentation M sM hM
      have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
      letI := @CanonicalStructure.normalize M sM
      exact ImaginaryBaseImages.preimage_definable (p := p) hp hf hVdef
    have hDef : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U ∩ f ⁻¹' V} := by
      apply FullBaseAtomicity.OverBase.congr (hUdef.inter hPre)
      intro z
      change (z 0 ∈ U ∧ z 0 ∈ A ∧ f (z 0) ∈ V) ↔ (z 0 ∈ U ∧ f (z 0) ∈ V)
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hUA h.1,h.2⟩⟩
    refine ⟨hWA,hDef,fun D hD => ?_⟩
    constructor
    · exact fun ho => hUOpen D (fun x hx => (hD hx).1) ho
    · intro ho
      have hDV : f '' D ⊆ V := by
        rintro y ⟨x,hx,rfl⟩
        exact (hD hx).2
      have hBack := hVOpen (f '' D) hDV ho
      have hEq : g '' (f '' D) = D := by
        apply Set.Subset.antisymm
        · rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
          have he : g (f z) = z := RVInverse.inverse_on hbij.2.1 (hWA (hD hz))
          exact Eq.mpr (congrArg (fun w : M => w ∈ D) he) hz
        · intro x hx
          exact ⟨f x,⟨x,hx,rfl⟩,RVInverse.inverse_on hbij.2.1 (hWA (hD hx))⟩
      exact hEq ▸ hBack
  have hCov (a : M) (ha : a ∈ A) : ∃ W ∈ H, a ∈ W := by
    obtain ⟨U,hU,haU⟩ := hCovF a ha
    obtain ⟨V,hV,hfaV⟩ := hCovG (f a) (hbij.1 ha)
    exact ⟨U ∩ f ⁻¹' V,(hMem _).mpr ⟨U,hU,V,hV,rfl⟩,haU,hfaV⟩
  exact OpenToOpenPartitions.exists_partition B hA f H hH hCov

theorem proposition_3_19 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A C : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAVF : A ⊆ {x | iVF x}) (hCVF : C ⊆ {x | iVF x})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A C) :
    ∃ P : Finset (Set M),
      (∀ U ∈ P, U.Nonempty ∧ U ⊆ A ∧
        FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
        MaximalOpenClasses.OpenToOpen U f) ∧
      (P : Set (Set M)).Pairwise Disjoint ∧ A = {x | ∃ U ∈ P, x ∈ U} := by
  classical
  obtain ⟨FA,hFA,hAData⟩ := hA
  obtain ⟨FF,hFF,hFData⟩ := hf
  obtain ⟨FG,hFG,hGData⟩ := hδ
  let F := (FA ∪ FF) ∪ FG
  let B0 : FullBaseAtomicity.Base (M := M) := ⟨B.real,(F : Set (ParameterPresentation.Name (M := M)))⟩
  have hA0 : FullBaseAtomicity.OverBase B0 {z : Fin 1 → M | z 0 ∈ A} :=
    ⟨FA,fun i hi => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hi))),hAData⟩
  have hf0 : FullBaseAtomicity.OverBase B0 (ImaginaryBaseImages.graphOn A f) :=
    ⟨FF,fun i hi => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hi))),hFData⟩
  have hδ0 : FullGammaSyntax.Scalar B0 {δ} :=
    ⟨FG,fun i hi => Finset.mem_union.mpr (Or.inr hi),hGData⟩
  have hB0 : B0.imaginary ⊆ B.imaginary := by
    intro i hi
    change i ∈ (FA ∪ FF) ∪ FG at hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact hFA i hi
      · exact hFF i hi
    · exact hFG i hi
  obtain ⟨P,hP,hDis,hEq⟩ := proposition_3_19_finite_base hκ hs B0 F.finite_toSet hsmall
    h00 δ hδ0 hδ1 hA0 hAVF hCVF f hf0 hbij
  refine ⟨P,?_,hDis,hEq⟩
  intro U hU
  obtain ⟨hne,hUA,hDef,hOpen⟩ := hP U hU
  exact ⟨hne,hUA,FullBaseAtomicity.OverBase.mono hDef Set.Subset.rfl hB0,hOpen⟩

end IntegrationInACVF.Section3ACVF.FullOpenToOpenPartition
