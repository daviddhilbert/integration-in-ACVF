module

public import IntegrationSection3.FiniteFieldDefinableMaps
public import Mathlib.FieldTheory.IntermediateField.Algebraic

@[expose] public section

/-! Over an algebraic extension of a finite field, every injective
definable self-map of a finite-dimensional definable set is surjective.
The finite restriction follows the finite-adjoin construction in Mathlib's
Apache-2.0 FieldTheory/AxGrothendieck.lean, with definable-map preservation
proved via the finite-field Frobenius rather than assumed polynomiality. -/

open Set Classical FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section3.LocallyFiniteDefinableInjection

theorem surjOn_of_injOn {K F₀ ι : Type*} [Field F₀] [Finite F₀]
    [Field K] [Algebra F₀ K] [alg : Algebra.IsAlgebraic F₀ K]
    [FirstOrder.Ring.CompatibleRing K] [Finite ι]
    (C : Set K) (S : Set (ι → K)) (f : (ι → K) → (ι → K))
    (hf : C.Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)})
    (hm : S.MapsTo f S) (hinj : S.InjOn f) : S.SurjOn f S := by
  classical
  obtain ⟨c,_,hcf⟩ := Set.definable_iff_finitely_definable.mp hf
  intro v hvS
  letI := Fintype.ofFinite ι
  let s : Finset K := c ∪ Finset.univ.image v
  have is_int : ∀ x : K, IsIntegral F₀ x := fun x =>
    isAlgebraic_iff_isIntegral.mp (alg.isAlgebraic x)
  haveI := isNoetherian_adjoin_finset s (fun x _ => is_int x)
  haveI : Finite (Algebra.adjoin F₀ (s : Set K)) := Module.finite_of_finite F₀
  have hAlg : (Algebra.adjoin F₀ (s : Set K)).IsAlgebraic :=
    fun x _ => alg.isAlgebraic x
  let F : IntermediateField F₀ K := hAlg.toIntermediateField
  haveI : Finite F := inferInstanceAs (Finite (Algebra.adjoin F₀ (s : Set K)))
  letI := Fintype.ofFinite F
  have hC : (c : Set K) ⊆ (algebraMap F K).range := by
    intro x hx
    have hmem : x ∈ F := Algebra.subset_adjoin (Finset.mem_union_left _ hx)
    exact ⟨⟨x,hmem⟩,rfl⟩
  have hv (i : ι) : v i ∈ F :=
    Algebra.subset_adjoin (Finset.mem_union_right c (Finset.mem_image_of_mem v (Finset.mem_univ i)))
  have hfF (x : ι → F) (hx : (fun i => (x i).val) ∈ S) :
      ∀ i, f (fun i => (x i).val) i ∈ F := by
    have hRange := FiniteFieldDefinableMaps.mapsTo_finite_subfield (F := F) (c : Set K) hC S f hcf
      (fun i => (x i).val) hx (fun i => ⟨x i,rfl⟩)
    intro i
    obtain ⟨y,hy⟩ := hRange i
    exact hy ▸ y.property
  let S' : Set (ι → F) := {x | (fun i => (x i).val) ∈ S}
  let res : S' → S' := fun x =>
    ⟨fun i => ⟨f (fun i => (x.val i).val) i,hfF x.val x.property i⟩,hm x.property⟩
  have hres : Function.Injective res := by
    intro x y hxy
    have he : f (fun i => (x.val i).val) = f (fun i => (y.val i).val) := by
      funext i
      exact congrArg (fun u : S' => (u.val i).val) hxy
    have h := hinj x.property y.property he
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun h i)
  have hresSurj : Function.Surjective res := (Finite.injective_iff_surjective).mp hres
  obtain ⟨w,hw⟩ := hresSurj (⟨fun i => ⟨v i,hv i⟩,hvS⟩ : S')
  refine ⟨(fun i => (w.val i).val),w.property,?_⟩
  funext i
  exact congrArg (fun u : S' => (u.val i).val) hw

end IntegrationInACVF.Section3.LocallyFiniteDefinableInjection
