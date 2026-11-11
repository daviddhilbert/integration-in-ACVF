import IntegrationSection3ACVF.VFExchangeAnyBase
import IntegrationSection3ACVF.FullBaseDefinability
import Section3.AlgebraicFinite
import Section3.NormalizationSaturation
import Section3.SmallFiniteParameters

/-! Finite fibres of a real-parameter definable function above a
nonalgebraic value. Imaginary parameters may restrict the source set;
their finite codes are specialized only in the finiteness proof. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FiniteFibresFromExchange

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem output_algebraic (S : Set M) {D : Set M} (f : M → M)
    (hf : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn D f))
    (x : VFType (M := M)) (hx : x.val ∈ D) (hy : iVF (f x.val)) :
    AlgebraicAt (insert x.val S) .vf (f x.val) := by
  have hSingle : @Set.Definable₁ M (insert x.val S) LRV (CanonicalStructure.normalize (M := M)) {f x.val} := by
    letI := @CanonicalStructure.normalize M sM
    have hm : (insert x.val S).DefinableMap LRV
        (fun z : Fin 1 → M => ![x.val,z 0]) := by
      intro j
      fin_cases j
      · exact LRV.definableFun_const (Fin 1) (Set.mem_insert _ _)
      · exact Set.DefinableFun.proj LRV
    have h := (hf.mono (Set.subset_insert x.val S)).preimage_map hm
    change (insert x.val S).Definable LRV {z : Fin 1 → M | z 0 ∈ ({f x.val} : Set M)}
    convert h using 1
    ext z
    change (z 0 = f x.val) ↔ (x.val ∈ D ∧ z 0 = f x.val)
    exact (and_iff_right hx).symm
  refine ⟨{f x.val},?_,Set.finite_singleton _,rfl⟩
  exact (@definableAt_iff_normalized_raw M sM hM (insert x.val S) .vf _).mpr
    ⟨hSingle,by rintro z rfl; exact hy⟩

theorem inverse_algebraic (S : Set M) {D : Set M} (f : M → M)
    (hf : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn D f))
    (x : VFType (M := M)) (hx : x.val ∈ D) (hy : iVF (f x.val))
    (hna : ¬ AlgebraicAt S .vf (f x.val)) :
    AlgebraicAt (insert (f x.val) S) .vf x.val := by
  exact VFExchangeAnyBase.exchange S (⟨f x.val,hy⟩ : VFType (M := M)) x
    (output_algebraic S f hf x hx hy) hna

theorem finite_fibres {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {A : Set M} (hAVF : A ⊆ {x | iVF x}) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hAlg : ∀ (x : VFType (M := M)), x.val ∈ A →
      AlgebraicAt (insert (f x.val) B.real) .vf x.val) :
    ∀ y : M, {x : M | x ∈ A ∧ f x = y}.Finite := by
  have hex : ∃ F : Set M, F.Finite ∧
      @Set.Definable M (B.real ∪ F) LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
        (ImaginaryBaseImages.graphOn A f) := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hf
  obtain ⟨F,hF,hd⟩ := hex
  intro y
  let T := B.real ∪ insert y F
  let D : Set M := {x | x ∈ A ∧ f x = y}
  have hsmallT : Cardinal.mk T < κ := small_union_finite hκ B.real hsmall _ (hF.insert y)
  have hST : B.real ∪ F ⊆ T := fun _ h => h.elim Or.inl (fun h => Or.inr (Or.inr h))
  have hBase : insert y B.real ⊆ T := fun _ h => h.elim (fun he => Or.inr (Or.inl he)) Or.inl
  have hD : @Set.Definable₁ M T LRV (CanonicalStructure.normalize (M := M)) D := by
    letI := @CanonicalStructure.normalize M sM
    have hm : T.DefinableMap LRV (fun z : Fin 1 → M => ![z 0,y]) := by
      intro j
      fin_cases j
      · exact Set.DefinableFun.proj LRV
      · exact LRV.definableFun_const (Fin 1) (Or.inr (Set.mem_insert y F))
    change T.Definable LRV {z : Fin 1 → M | z 0 ∈ D}
    convert (hd.mono hST).preimage_map hm using 1
    ext z
    change (z 0 ∈ A ∧ f (z 0) = y) ↔ (z 0 ∈ A ∧ y = f (z 0))
    exact and_congr_right (fun _ => eq_comm)
  have hAll : ∀ x ∈ D, @RawClosure.AlgebraicOver M (CanonicalStructure.normalize (M := M)) T x := by
    intro x hx
    have ha := hAlg (⟨x,hAVF hx.1⟩ : VFType (M := M)) hx.1
    change AlgebraicAt (insert (f x) B.real) .vf x at ha
    rw [hx.2] at ha
    obtain ⟨W,hW,hFin,hxW⟩ := ha
    have hw : @Set.Definable₁ M (insert y B.real) LRV (CanonicalStructure.normalize (M := M)) W :=
      ((@definableAt_iff_normalized_raw M sM hM _ .vf _).mp hW).1
    have hwT : @Set.Definable₁ M T LRV (CanonicalStructure.normalize (M := M)) W := by
      letI := @CanonicalStructure.normalize M sM
      exact hw.mono hBase
    exact ⟨W,hwT,hFin,hxW⟩
  have hsN := @Saturated.normalize M sM κ hs
  exact @RawClosure.finite_of_definable_subset_algebraic M (CanonicalStructure.normalize (M := M))
    κ hsN T hsmallT D hD hAll

end IntegrationInACVF.Section3ACVF.FiniteFibresFromExchange
