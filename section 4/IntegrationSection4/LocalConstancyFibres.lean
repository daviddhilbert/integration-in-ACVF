import IntegrationSection4.LocalConstancySyntax
import IntegrationSection4.EmptyInteriorFinite
import IntegrationSection3ACVF.FiniteFibresFromExchange
import IntegrationSection3ACVF.RealParameterTuples
import IntegrationSection3ACVF.SeparationFunctions

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.LocalConstancyFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)

private theorem real_of_empty (S : Set M) {ι : Type} [Finite ι] {D : Set (ι → M)}
    (hD : FullBaseAtomicity.OverBase (⟨S,∅⟩ : FullBaseAtomicity.Base (M := M)) D) :
    @Set.Definable M S LRV N ι D := by
  let p := @ParameterPresentation.presentation M sM hM
  letI := N
  exact (ImaginaryParameters.OverBase.empty_iff_real (p := p) rfl).mp hD

/-- Outside the locally constant locus, every actual function fibre is finite. -/
theorem finite_fibres_off_locus (S A : Set M) (hAVF : A ⊆ {x | iVF x}) (f : M → M)
    (hf : @Set.Definable M S LRV N (Fin 2) (ImaginaryBaseImages.graphOn A f)) :
    ∀ y, {x | x ∈ A \ LocalConstancySyntax.locus A f ∧ f x = y}.Finite := by
  let B : FullBaseAtomicity.Base (M := M) := ⟨S,∅⟩
  have hF : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f) := FullBaseAtomicity.OverBase.of_real hf
  have hE := LocalConstancySyntax.locus_definable B A f hF
  have hEraw := real_of_empty S hE
  intro y
  let U := {x | x ∈ A \ LocalConstancySyntax.locus A f ∧ f x = y}
  have hRaw : @Set.Definable₁ M (insert y S) LRV N U := by
    letI := N
    have hm : (insert y S).DefinableMap LRV (fun z : Fin 1 → M => ![z 0,y]) := by
      intro i
      fin_cases i
      · exact Set.DefinableFun.proj LRV
      · exact LRV.definableFun_const (Fin 1) (Set.mem_insert y S)
    have hh := ((hf.mono (Set.subset_insert y S)).preimage_map hm).inter
      (hEraw.mono (Set.subset_insert y S)).compl
    change (insert y S).Definable LRV {z : Fin 1 → M | z 0 ∈ U}
    convert hh using 1
    letI := sM
    ext z
    change ((z 0 ∈ A ∧ z 0 ∉ LocalConstancySyntax.locus A f) ∧ f (z 0) = y) ↔
      ((z 0 ∈ A ∧ y = f (z 0)) ∧ z 0 ∉ LocalConstancySyntax.locus A f)
    tauto
  have hU : DefinableAt (insert y S) .vf U :=
    (@definableAt_iff_normalized_raw M sM hM _ .vf U).mpr
      ⟨hRaw,fun _ hx => hAVF hx.1.1⟩
  apply EmptyInteriorFinite.finite_of_no_open _ U hU
  intro D hDo hDU
  obtain ⟨x,hx⟩ := RadiusPreparationGeometry.open_nonempty hDo
  have hxU := hDU hx
  apply hxU.1.2
  apply (LocalConstancySyntax.mem_iff A f x).mpr
  exact ⟨D,hDo,hx,fun z hz => (hDU hz).1.1,fun z hz => (hDU hz).2.trans hxU.2.symm⟩

/-- The image of the locally constant locus is finite. All algebraicity
and ball codes used in the argument remain internal. -/
theorem finite_image_on_locus {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (A : Set M)
    (hAVF : A ⊆ {x | iVF x}) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (hf : @Set.Definable M S LRV N (Fin 2) (ImaginaryBaseImages.graphOn A f)) :
    (f '' LocalConstancySyntax.locus A f).Finite := by
  let B : FullBaseAtomicity.Base (M := M) := ⟨S,∅⟩
  have hF : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f) := FullBaseAtomicity.OverBase.of_real hf
  have hAlg (y : M) (hy : y ∈ f '' LocalConstancySyntax.locus A f) : AlgebraicAt S .vf y := by
    by_contra hn
    obtain ⟨a,ha,hay⟩ := hy
    obtain ⟨D,hDo,haD,hDA,hConst⟩ := (LocalConstancySyntax.mem_iff A f a).mp ha
    obtain ⟨q,_,hBody⟩ := ParameterizedOpenImages.exists_open_code hDo
    let C := RealParameterTuples.extend B q
    have hDC : FullBaseAtomicity.OverBase C {z : Fin 1 → M | z 0 ∈ D} := by
      have hh := RealParameterTuples.specialize B q (OpenImageConfigurations.body_definable B)
      apply FullBaseAtomicity.OverBase.congr hh
      intro z
      change z 0 ∈ OpenImageConfigurations.body q ↔ z 0 ∈ D
      rw [hBody]
    have hFC := RealParameterTuples.mono B q hF
    have hGraphD : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn D f) := by
      have hh := FullBaseAtomicity.OverBase.inter
        (FullBaseAtomicity.OverBase.preimage_comp hDC (fun _ : Fin 1 => (0 : Fin 2))) hFC
      apply FullBaseAtomicity.OverBase.congr hh
      intro z
      change (z 0 ∈ D ∧ z 0 ∈ A ∧ z 1 = f (z 0)) ↔ (z 0 ∈ D ∧ z 1 = f (z 0))
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hDA h.1,h.2⟩⟩
    have hInvAlg (x : VFType (M := M)) (hx : x.val ∈ D) :
        AlgebraicAt (insert (f x.val) C.real) .vf x.val := by
      have hfy : f x.val = y := (hConst x.val hx).trans hay
      have hna : ¬ AlgebraicAt S .vf (f x.val) := hfy.symm ▸ hn
      obtain ⟨W,hW,hWf,hxW⟩ := FiniteFibresFromExchange.inverse_algebraic S f hf x (hDA hx) (hfVF _ (hDA hx)) hna
      refine ⟨W,DefinableAt.mono ?_ hW,hWf,hxW⟩
      exact Set.insert_subset_insert Set.subset_union_left
    have hFin := FiniteFibresFromExchange.finite_fibres hκ hs C
      (RealParameterTuples.small hκ B hsmall q) (fun _ hx => hAVF (hDA hx)) f hGraphD hInvAlg y
    have hDFin : D.Finite := hFin.subset (fun x hx => ⟨hx,(hConst x hx).trans hay⟩)
    exact (SeparationFunctions.open_infinite h00 δ hδ hDo) hDFin
  have hE := LocalConstancySyntax.locus_definable B A f hF
  have hGraphE : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (LocalConstancySyntax.locus A f) f) := by
    have hh := FullBaseAtomicity.OverBase.inter
      (FullBaseAtomicity.OverBase.preimage_comp hE (fun _ : Fin 1 => (0 : Fin 2))) hF
    apply FullBaseAtomicity.OverBase.congr hh
    intro z
    change (z 0 ∈ LocalConstancySyntax.locus A f ∧ z 0 ∈ A ∧ z 1 = f (z 0)) ↔
      (z 0 ∈ LocalConstancySyntax.locus A f ∧ z 1 = f (z 0))
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,LocalConstancySyntax.subset A f h.1,h.2⟩⟩
  have hImage : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ f '' LocalConstancySyntax.locus A f} := by
    letI := N
    exact ImaginaryBaseImages.image_definable hGraphE
  apply @RawClosure.finite_of_definable_subset_algebraic M N κ hs.normalize S hsmall
    (f '' LocalConstancySyntax.locus A f) (real_of_empty S hImage)
  intro y hy
  obtain ⟨W,hW,hWf,hyW⟩ := hAlg y hy
  exact ⟨W,((@definableAt_iff_normalized_raw M sM hM S .vf W).mp hW).1,hWf,hyW⟩

end IntegrationInACVF.Section4.LocalConstancyFibres
