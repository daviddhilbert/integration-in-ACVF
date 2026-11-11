import IntegrationSection3ACVF.PointwiseCoordinatePartitions
import IntegrationSection3ACVF.UniformPartitionTemplates

/-! Uniform finite formula templates for a selected pair of actual VF
coordinates in an otherwise mixed tuple bijection. Definable gluing into
whole-domain pieces is the next step of3.21. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.CoordinatePartitionTemplates

open PromotedPartitionTemplates

variable {M ι τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def graph (A : Set (ι → M)) (f : (ι → M) → (τ → M)) (i : ι) (j : τ) :
    Set (CoordinateFibreSyntax.Params i j ⊕ Fin 2 → M) :=
  {z | z (.inr 0) ∈ CoordinateFibres.source A f i j
    (fun k => z (.inl (.inl k))) (fun k => z (.inl (.inr k))) ∧
    z (.inr 1) = CoordinateFibres.map f i j (fun k => z (.inl (.inl k))) (z (.inr 0))}

theorem pointwise [Finite ι] [Finite τ] {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f))
    (hinj : Set.InjOn f A) (i : ι) (j : τ)
    (hSrcVF : ∀ x ∈ A, iVF (x i)) (hTarVF : ∀ x ∈ A, iVF (f x j))
    (p : CoordinateFibreSyntax.Params i j → M) :
    ∃ T : Template M (CoordinateFibreSyntax.Params i j), Definable B T ∧
      p ∈ locus (graph A f i j) T := by
  let u := p ∘ Sum.inl
  let v := p ∘ Sum.inr
  let D := CoordinateFibres.source A f i j u v
  let g := CoordinateFibres.map f i j u
  obtain ⟨P,hP,hDis,hCov⟩ := PointwiseCoordinatePartitions.exists_partition hκ hs B hsmall h00 δ hδ hδ1
    A f hf hinj i j hSrcVF hTarVF u v
  have hp : Sum.elim u v = p := by funext k; cases k <;> rfl
  have hP' : ∀ U ∈ P, U ⊆ D ∧
      FullBaseAtomicity.OverBase (RealParameterTuples.extend B p) {z : Fin 1 → M | z 0 ∈ U} ∧
      MaximalOpenClasses.OpenToOpen U g := by
    intro U hUP
    obtain ⟨_,hUD,hDef,hOpen⟩ := hP U hUP
    rw [hp] at hDef
    exact ⟨hUD,hDef,hOpen⟩
  exact of_partition B (graph A f i j) p D g (fun _ _ => Iff.rfl)
    (CoordinateFibres.map_injOn f hinj i j u v) P hP' hDis hCov

theorem finite_templates [Finite ι] [Finite τ] {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary.Finite)
    (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f))
    (hinj : Set.InjOn f A) (i : ι) (j : τ)
    (hSrcVF : ∀ x ∈ A, iVF (x i)) (hTarVF : ∀ x ∈ A, iVF (f x j)) :
    ∃ F : Finset (Template M (CoordinateFibreSyntax.Params i j)),
      (∀ T ∈ F, Definable B T) ∧
      ∀ p, ∃ T ∈ F, p ∈ locus (graph A f i j) T :=
  UniformPartitionTemplates.finite_templates hκ hs B hB hsmall (graph A f i j)
    (CoordinateFibreSyntax.graph_definable B A f hf i j)
    (pointwise hκ hs B hsmall h00 δ hδ hδ1 A f hf hinj i j hSrcVF hTarVF)

end IntegrationInACVF.Section3ACVF.CoordinatePartitionTemplates
