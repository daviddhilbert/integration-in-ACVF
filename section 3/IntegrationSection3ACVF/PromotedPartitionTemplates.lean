import IntegrationSection3ACVF.UnaryPartitionTemplates
import IntegrationSection3ACVF.RealParameterPromotion

/-! Actual finite scalar partitions, whose labels were named real
parameters, yield finite tuples of original-base formulas at those labels. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.PromotedPartitionTemplates

open UnaryRelationFamilies ParameterizedOpenImages UnaryPartitionTemplates

structure Template (M σ : Type) where
  size : ℕ
  cell : Fin size → Set (σ ⊕ Fin 1 → M)

variable {M σ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Definable (B : FullBaseAtomicity.Base (M := M)) (T : Template M σ) : Prop :=
  ∀ i, FullBaseAtomicity.OverBase B (T.cell i)

def locus (G : Set (σ ⊕ Fin 2 → M)) (T : Template M σ) : Set (σ → M) := valid G T.cell

theorem of_partition [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    (G : Set (σ ⊕ Fin 2 → M)) (p : σ → M) (A : Set M) (f : M → M)
    (hG : ∀ x y, pair p x y ∈ G ↔ x ∈ A ∧ y = f x) (hinj : Set.InjOn f A)
    (P : Finset (Set M))
    (hP : ∀ U ∈ P, U ⊆ A ∧
      FullBaseAtomicity.OverBase (RealParameterTuples.extend B p) {z : Fin 1 → M | z 0 ∈ U} ∧
      MaximalOpenClasses.OpenToOpen U f)
    (hDis : (P : Set (Set M)).Pairwise Disjoint)
    (hCov : A = {x | ∃ U ∈ P, x ∈ U}) :
    ∃ T : Template M σ, Definable B T ∧ p ∈ locus G T := by
  classical
  choose R hR hAt using fun U : P =>
    RealParameterPromotion.promote_finite B p (hP U.val U.property).2.1
  let e := Fintype.equivFin P
  let T : Template M σ := ⟨Fintype.card P,fun i => R (e.symm i)⟩
  have hCell (i : Fin T.size) : fibre (T.cell i) p = (e.symm i).val := by
    ext x
    exact Set.ext_iff.mp (hAt (e.symm i)) ![x]
  refine ⟨T,fun i => hR (e.symm i),?_⟩
  apply (valid_iff G T.cell p A f hG hinj).mpr
  refine ⟨?_,?_,?_⟩
  · intro x
    rw [hCov]
    constructor
    · rintro ⟨U,hUP,hxU⟩
      refine ⟨e ⟨U,hUP⟩,?_⟩
      rw [hCell]
      simpa only [e.symm_apply_apply] using hxU
    · rintro ⟨i,hxi⟩
      exact ⟨(e.symm i).val,(e.symm i).property,(Set.ext_iff.mp (hCell i) x).mp hxi⟩
  · intro i j hij
    rw [hCell i,hCell j]
    have he : (e.symm i).val ≠ (e.symm j).val := by
      intro he
      have hs : e.symm i = e.symm j := Subtype.ext he
      exact hij (e.symm.injective hs)
    exact hDis (e.symm i).property (e.symm j).property he
  · intro i
    rw [hCell]
    exact (hP (e.symm i).val (e.symm i).property).2.2

end IntegrationInACVF.Section3ACVF.PromotedPartitionTemplates
