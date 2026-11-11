import IntegrationSection3ACVF.CoordinateFibreSyntax
import IntegrationSection3ACVF.CoordinateOpenToOpen
import IntegrationSection3ACVF.RealParameterTuples
import IntegrationSection3ACVF.FullOpenToOpenPartition

/-! The pointwise finite partitions used in3.21,for actual mixed tuple
maps. Context labels are finitely named real parameters. Uniformity in
those labels is a separate remaining step,not an input disguised as proof. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.PointwiseCoordinatePartitions

variable {M ι τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_partition [Finite ι] [Finite τ] {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f))
    (hinj : Set.InjOn f A) (i : ι) (j : τ)
    (hSrcVF : ∀ x ∈ A, iVF (x i)) (hTarVF : ∀ x ∈ A, iVF (f x j))
    (u : CoordinateSlices.Other i → M) (v : CoordinateSlices.Other j → M) :
    ∃ P : Finset (Set M),
      (∀ U ∈ P, U.Nonempty ∧ U ⊆ CoordinateFibres.source A f i j u v ∧
        FullBaseAtomicity.OverBase (RealParameterTuples.extend B (Sum.elim u v))
          {z : Fin 1 → M | z 0 ∈ U} ∧
        MaximalOpenClasses.OpenToOpen U (CoordinateFibres.map f i j u)) ∧
      (P : Set (Set M)).Pairwise Disjoint ∧
      CoordinateFibres.source A f i j u v = {x | ∃ U ∈ P, x ∈ U} := by
  let w : CoordinateFibreSyntax.Params i j → M := Sum.elim u v
  let C := RealParameterTuples.extend B w
  let D := CoordinateFibres.source A f i j u v
  let g := CoordinateFibres.map f i j u
  have hGraph : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn D g) := by
    have hu := CoordinateFibreSyntax.graph_definable B A f hf i j
    have h := RealParameterTuples.specialize B w hu
    apply FullBaseAtomicity.OverBase.congr h
    intro z
    rfl
  have hD : FullBaseAtomicity.OverBase C {z : Fin 1 → M | z 0 ∈ D} := by
    have h := FullBaseAtomicity.OverBase.exists_block
      (FullBaseAtomicity.OverBase.preimage_comp hGraph (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1))
    apply FullBaseAtomicity.OverBase.congr h
    intro z
    change (∃ y : Fin 1 → M, z 0 ∈ D ∧ y 0 = g (z 0)) ↔ z 0 ∈ D
    exact ⟨fun ⟨_,hz,_⟩ => hz,fun hz => ⟨![g (z 0)],hz,rfl⟩⟩
  have hDVF (x : M) (hx : x ∈ D) : iVF x := by
    have h := hSrcVF (CoordinateSlices.insert i u x) hx.1
    simpa only [CoordinateSlices.insert_same] using h
  have hImageVF : g '' D ⊆ {x | iVF x} := by
    rintro y ⟨x,hx,rfl⟩
    exact hTarVF (CoordinateSlices.insert i u x) hx.1
  have hInj : Set.InjOn g D := CoordinateFibres.map_injOn f hinj i j u v
  have hBij : Set.BijOn g D (g '' D) :=
    ⟨fun x hx => ⟨x,hx,rfl⟩,hInj,fun y hy => hy⟩
  have hδC : FullGammaSyntax.Scalar C {δ} := RealParameterTuples.mono B w hδ
  exact FullOpenToOpenPartition.proposition_3_19 hκ hs C (RealParameterTuples.small hκ B hsmall w)
    h00 δ hδC hδ1 hD hDVF hImageVF g hGraph hBij

end IntegrationInACVF.Section3ACVF.PointwiseCoordinatePartitions
