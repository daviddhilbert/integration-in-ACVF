import IntegrationSection4.FiniteScalarFamilies
import IntegrationSection3ACVF.SingleCoordinatePartition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FamilyOpenPartition

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def tupleMap {n : ℕ} (f : (Fin n → M) → M → M) (w : Fin n ⊕ Fin 1 → M) : Fin n ⊕ Fin 1 → M :=
  Sum.elim (w ∘ Sum.inl) (fun _ => f (w ∘ Sum.inl) (w (.inr 0)))

theorem tuple_graph {n : ℕ} (B : FullBaseAtomicity.Base (M := M))
    (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (hf : FiniteScalarFamilies.Graph B A f) :
    FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph
      {w : Fin n ⊕ Fin 1 → M | w (.inr 0) ∈ A (w ∘ Sum.inl)} (tupleMap f)) := by
  let ι := (Fin n ⊕ Fin 1) ⊕ (Fin n ⊕ Fin 1)
  have hFun := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim Sum.inl (fun _ => .inr (.inr 0)) : (Fin n ⊕ Fin 1) ⊕ Fin 1 → ι)
  have hEq (i : Fin n) : FullBaseAtomicity.OverBase B {z : ι → M | z (.inr (.inl i)) = z (.inl (.inl i))} := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact RawClosure.definable_equal_coordinates B.real _ _
  have hAll := FullBaseAtomicity.OverBase.forall_finite hEq
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hFun hAll)
  intro z
  change ((z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
    z (.inr (.inr 0)) = f (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))) ∧
    (∀ i : Fin n, z (.inr (.inl i)) = z (.inl (.inl i)))) ↔
      (z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧ z ∘ Sum.inr = tupleMap f (z ∘ Sum.inl))
  constructor
  · rintro ⟨⟨hx,hy⟩,h⟩
    refine ⟨hx,funext fun i => ?_⟩
    cases i with
    | inl i => exact h i
    | inr i => fin_cases i; exact hy
  · rintro ⟨hx,he⟩
    exact ⟨⟨hx,congrFun he (.inr 0)⟩,fun i => congrFun he (.inl i)⟩

theorem exists_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ) {n : ℕ}
    (A : (Fin n → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin n → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hf : FiniteScalarFamilies.Graph B A f) (hInj : ∀ p, Set.InjOn (f p) (A p)) :
    ∃ P : Finset (Set (Fin n ⊕ Fin 1 → M)),
      (∀ W ∈ P, W.Nonempty ∧
        W ⊆ {w | w (.inr 0) ∈ A (w ∘ Sum.inl)} ∧ FullBaseAtomicity.OverBase B W ∧
        ∀ p : Fin n → M, MaximalOpenClasses.OpenToOpen
          {x | Sum.elim p (fun _ : Fin 1 => x) ∈ W} (f p)) ∧
      (∀ p x, x ∈ A p ↔ ∃ W ∈ P, Sum.elim p (fun _ : Fin 1 => x) ∈ W) := by
  let U := {w : Fin n ⊕ Fin 1 → M | w (.inr 0) ∈ A (w ∘ Sum.inl)}
  have hInj' : Set.InjOn (tupleMap f) U := by
    intro w hw v hv he
    have hp : w ∘ Sum.inl = v ∘ Sum.inl := funext fun i => congrFun he (.inl i)
    have hfv := congrFun he (.inr 0)
    change f (w ∘ Sum.inl) (w (.inr 0)) = f (v ∘ Sum.inl) (v (.inr 0)) at hfv
    change w (.inr 0) ∈ A (w ∘ Sum.inl) at hw
    change v (.inr 0) ∈ A (v ∘ Sum.inl) at hv
    rw [← hp] at hv hfv
    have hx := hInj _ hw hv hfv
    funext i
    cases i with
    | inl i => exact congrFun hp i
    | inr i => fin_cases i; exact hx
  obtain ⟨P,hP,_,hCover⟩ := SingleCoordinatePartition.full_base hκ hs B hsmall h00 δ hδ hδ1
    U (tupleMap f) (tuple_graph B A f hf) hInj' (.inr 0) (.inr 0)
    (fun w hw => hAVF _ hw) (fun w hw => hfVF _ _ hw)
  refine ⟨P,?_,?_⟩
  · intro W hW
    obtain ⟨hne,hWA,hDef,hAt⟩ := hP W hW
    refine ⟨hne,hWA,hDef,fun p => ?_⟩
    let u := CoordinateSlices.tail (Sum.inr (0 : Fin 1)) (Sum.elim p (fun _ : Fin 1 => iVFZero))
    have hIns (x : M) : CoordinateSlices.insert (.inr 0) u x = Sum.elim p (fun _ : Fin 1 => x) := by
      funext i
      cases i with
      | inl i => simp [CoordinateSlices.insert,u,CoordinateSlices.tail]
      | inr i => fin_cases i; exact CoordinateSlices.insert_same _ _ _
    have hTail (x : M) : CoordinateSlices.tail (.inr 0) (tupleMap f (Sum.elim p (fun _ : Fin 1 => x))) = u := by
      funext j
      obtain ⟨j,hj⟩ := j
      cases j with
      | inl i => rfl
      | inr i => fin_cases i; exact (hj rfl).elim
    have hSource : CoordinateFibres.source W (tupleMap f) (.inr 0) (.inr 0) u u =
        {x | Sum.elim p (fun _ : Fin 1 => x) ∈ W} := by
      ext x
      change (CoordinateSlices.insert (.inr 0) u x ∈ W ∧
        CoordinateSlices.tail (.inr 0) (tupleMap f (CoordinateSlices.insert (.inr 0) u x)) = u) ↔ _
      rw [hIns,hTail]
      simp only [Set.mem_setOf_eq,and_true]
    have hMap : CoordinateFibres.map (tupleMap f) (.inr 0) (.inr 0) u = f p := by
      funext x
      change tupleMap f (CoordinateSlices.insert (.inr 0) u x) (.inr 0) = f p x
      rw [hIns]
      rfl
    have hh := hAt u u
    rwa [hSource,hMap] at hh
  · intro p x
    have hh := Set.ext_iff.mp hCover (Sum.elim p (fun _ : Fin 1 => x))
    exact hh

end IntegrationInACVF.Section4.FamilyOpenPartition
