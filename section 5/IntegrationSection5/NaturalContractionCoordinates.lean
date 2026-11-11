import IntegrationSection5.NaturalContractionMap
import IntegrationSection5.RelativeInverseGeometry

/-! The coordinate-injectivity observation following Definition5.5.
Actual unary fibre specials give an exact difference identity on every
vertical line of a fixed final RV-label tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}

theorem HeadPreparation.contractionMap_vf {A : DefSet (M := M) S (n+1) m}
    (T : HeadPreparation A) (a : A) (j : Fin n) :
    vfAt (T.contractionMap a).val j = vfAt a.val j.succ := by
  have h := congrArg (fun p : Point (M := M) n (1+T.arity) => vfAt p j)
    (headKeyMap_apply T.target (T.map a))
  exact h.trans (T.special.choose a j.succ (Fin.succ_ne_zero j))

namespace OrderedContractionProgram
variable {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}

theorem naturalMap_coordinate_difference (T : OrderedContractionProgram S A U) (a b : A) (i : Fin n)
    (hlabels : (T.naturalMap a).val.2 = (T.naturalMap b).val.2)
    (hOther : ∀ j : Fin n, j ≠ i → vfAt (T.naturalMap a).val j = vfAt (T.naturalMap b).val j) :
    vfAt a.val i-vfAt b.val i = vfAt (T.naturalMap a).val i-vfAt (T.naturalMap b).val i := by
  induction T with
  | zero A => exact Fin.elim0 i
  | @step n m l A U T tail ih =>
    cases i using Fin.cases with
    | zero =>
      have hTail : tail.naturalMap (T.contractionMap a) = tail.naturalMap (T.contractionMap b) := by
        apply Subtype.ext
        refine Prod.ext ?_ hlabels
        funext j
        exact hOther j.succ (Fin.succ_ne_zero j)
      have hContract := tail.naturalMap_injective hTail
      have hPair := (T.contractionMap_eq_iff a b).mp hContract
      have hd := T.inverse_difference (T.map a) (T.map b) hPair.1 ((sameRV_iff _ _).mp hPair.2).2
      rw [T.inverse_apply,T.inverse_apply] at hd
      exact hd
    | succ i =>
      have hOtherTail : ∀ j : Fin n, j ≠ i →
          vfAt (tail.naturalMap (T.contractionMap a)).val j = vfAt (tail.naturalMap (T.contractionMap b)).val j :=
        fun j hj => hOther j.succ (Fin.succ_inj.ne.mpr hj)
      have hd := ih (T.contractionMap a) (T.contractionMap b) i hlabels hOtherTail
      rw [T.contractionMap_vf,T.contractionMap_vf] at hd
      exact hd

/-- On the preimage of any final vertical line with fixed RV labels, the
corresponding original VF coordinate is injective. This includes the
single-nonzero-coordinate RV cells used in5.6. -/
theorem original_coordinate_injective_on_final_line (T : OrderedContractionProgram S A U)
    (a b : A) (i : Fin n) (hlabels : (T.naturalMap a).val.2 = (T.naturalMap b).val.2)
    (hOther : ∀ j : Fin n, j ≠ i → vfAt (T.naturalMap a).val j = vfAt (T.naturalMap b).val j)
    (hi : vfAt a.val i = vfAt b.val i) : a = b := by
  have hd := T.naturalMap_coordinate_difference a b i hlabels hOther
  rw [hi,sub_self] at hd
  have hNew : vfAt (T.naturalMap a).val i = vfAt (T.naturalMap b).val i := sub_eq_zero.mp hd.symm
  apply T.naturalMap_injective
  apply Subtype.ext
  refine Prod.ext ?_ hlabels
  funext j
  by_cases hj : j = i
  · subst j; exact hNew
  · exact hOther j hj

end OrderedContractionProgram
end IntegrationInACVF.Section5
