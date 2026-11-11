import IntegrationSection3ACVF.RadialClassMaps
import IntegrationSection3ACVF.RealParameterTuples

/-! The graph induced on translated RV classes is the actual existential
image of the whole partial VF graph. Only the two hole-centre labels are
adjoined as real parameters; no chosen quotient representatives are named. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RadialQuotientGraph

open RadialOpenClasses RVDifferencePairs

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def relation (H : Set (Fin 2 → M)) : Set (Fin 2 ⊕ Fin 2 → M) :=
  {z | ∃ w : Fin 2 → M, w ∈ H ∧
    z (.inr 0) = difference (w 0) (z (.inl 0)) ∧ z (.inr 1) = difference (w 1) (z (.inl 1))}

theorem relation_definable (B : FullBaseAtomicity.Base (M := M)) {H : Set (Fin 2 → M)}
    (hH : FullBaseAtomicity.OverBase B H) : FullBaseAtomicity.OverBase B (relation H) := by
  let πG : Fin 2 → (Fin 2 ⊕ Fin 2) ⊕ Fin 2 := Sum.inr
  let πA : Fin 3 → (Fin 2 ⊕ Fin 2) ⊕ Fin 2 := ![.inr 0,.inl (.inl 0),.inl (.inr 0)]
  let πB : Fin 3 → (Fin 2 ⊕ Fin 2) ⊕ Fin 2 := ![.inr 1,.inl (.inl 1),.inl (.inr 1)]
  have heG (z : Fin 2 ⊕ Fin 2 → M) (w : Fin 2 → M) : Sum.elim z w ∘ πG = w := rfl
  have heA (z : Fin 2 ⊕ Fin 2 → M) (w : Fin 2 → M) :
      Sum.elim z w ∘ πA = ![w 0,z (.inl 0),z (.inr 0)] := by funext k; fin_cases k <;> rfl
  have heB (z : Fin 2 ⊕ Fin 2 → M) (w : Fin 2 → M) :
      Sum.elim z w ∘ πB = ![w 1,z (.inl 1),z (.inr 1)] := by funext k; fin_cases k <;> rfl
  have hDiff := difference_graph_definable B
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hH πG)
    (FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.preimage_comp hDiff πA)
      (FullBaseAtomicity.OverBase.preimage_comp hDiff πB)))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ w : Fin 2 → M, Sum.elim z w ∘ πG ∈ H ∧
    Sum.elim z w ∘ πA ∈ {u | u 2 = difference (u 0) (u 1)} ∧
    Sum.elim z w ∘ πB ∈ {u | u 2 = difference (u 0) (u 1)}) ↔ _
  simp_rw [heG,heA,heB]
  rfl

theorem graph_definable (B : FullBaseAtomicity.Base (M := M)) (a b : M)
    {A U : Set M} (f g : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hGraph : ∀ u v, (u ∈ U ∧ v = g u) ↔ ∃ x ∈ A, difference x a = u ∧ difference (f x) b = v) :
    FullBaseAtomicity.OverBase (RealParameterTuples.extend B ![a,b]) (ImaginaryBaseImages.graphOn U g) := by
  have hd := RealParameterTuples.specialize B ![a,b] (relation_definable B hf)
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ w : Fin 2 → M, (w 0 ∈ A ∧ w 1 = f (w 0)) ∧
    z 0 = difference (w 0) a ∧ z 1 = difference (w 1) b) ↔ (z 0 ∈ U ∧ z 1 = g (z 0))
  rw [hGraph]
  constructor
  · rintro ⟨w,⟨hx,hy⟩,hu,hv⟩
    exact ⟨w 0,hx,hu.symm,hy ▸ hv.symm⟩
  · rintro ⟨x,hx,hu,hv⟩
    exact ⟨![x,f x],⟨hx,rfl⟩,hu.symm,hv.symm⟩

theorem exists_definable_rv_bijection (B : FullBaseAtomicity.Base (M := M))
    (a b : VFType (M := M)) (V W : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) (hW : Values.infinity ∉ W) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (domain a V) f))
    (hbij : Set.BijOn f (domain a V) (domain b W))
    (hoo : MaximalOpenClasses.OpenToOpen (domain a V) f) :
    ∃ g : M → M,
      Set.BijOn g ((fun x => difference x a.val) '' domain a V) ((fun y => difference y b.val) '' domain b W) ∧
      FullBaseAtomicity.OverBase (RealParameterTuples.extend B ![a.val,b.val])
        (ImaginaryBaseImages.graphOn ((fun x => difference x a.val) '' domain a V) g) ∧
      ∀ x ∈ domain a V, g (difference x a.val) = difference (f x) b.val := by
  obtain ⟨g,hg,hFactor,hGraph⟩ := RadialClassMaps.exists_rv_bijection a b V W hV hW f hbij hoo
  exact ⟨g,hg,graph_definable B a.val b.val f g hf hGraph,hFactor⟩

end IntegrationInACVF.Section3ACVF.RadialQuotientGraph
