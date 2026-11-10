import IntegrationSection3ACVF.FullBaseDefinability
import IntegrationSection3ACVF.OpenBallConstancy
import IntegrationSection3.PairMapFibres

/-! Full-base definability of the pair of RV difference values for a
VF map. The normalized total term agrees with the original interpretation
on the actual VF sort; all imaginary codes remain in the graph. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVDifferencePairs

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def difference (x y : M) : M :=
  @iRv M (CanonicalStructure.normalize (M := M))
    (@iVFAdd M (CanonicalStructure.normalize (M := M)) x
      (@iVFNeg M (CanonicalStructure.normalize (M := M)) y))

theorem difference_vf (x y : VFType (M := M)) :
    difference x.val y.val = iRv (x-y).val := by
  have hn : @iVFNeg M (CanonicalStructure.normalize (M := M)) y.val = iVFNeg y.val :=
    CanonicalStructure.normalize_fun Fn.vfNeg ![y.val] (fun i => by fin_cases i; exact y.property)
  have ha : @iVFAdd M (CanonicalStructure.normalize (M := M)) x.val (iVFNeg y.val) =
      iVFAdd x.val (iVFNeg y.val) :=
    CanonicalStructure.normalize_fun Fn.vfAdd ![x.val,iVFNeg y.val] (fun i => by
      fin_cases i
      · exact x.property
      · exact vf_neg_mem hM y.property)
  have hr : @iRv M (CanonicalStructure.normalize (M := M)) (iVFAdd x.val (iVFNeg y.val)) =
      iRv (iVFAdd x.val (iVFNeg y.val)) :=
    CanonicalStructure.normalize_fun Fn.rvMap ![iVFAdd x.val (iVFNeg y.val)] (fun i => by
      fin_cases i
      exact vf_add_mem hM x.property (vf_neg_mem hM y.property))
  unfold difference
  rw [hn,ha,hr,sub_eq_add_neg]
  rfl

theorem difference_graph_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {z : Fin 3 → M | z 2 = difference (z 0) (z 1)} := by
  apply FullBaseAtomicity.OverBase.of_real
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hn : B.real.DefinableFun LRV (fun z : Fin 3 → M => iVFNeg (z 1)) := by
    have h : B.real.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfNeg) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 1 Fn.vfNeg)
    exact h.comp (fun i => by fin_cases i; exact Set.DefinableFun.proj LRV)
  have ha : B.real.DefinableFun LRV (fun z : Fin 3 → M => iVFAdd (z 0) (iVFNeg (z 1))) := by
    have h : B.real.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfAdd) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 2 Fn.vfAdd)
    exact h.comp (fun i => by
      fin_cases i
      · exact Set.DefinableFun.proj LRV
      · exact hn)
  have hr : B.real.DefinableFun LRV
      (fun z : Fin 3 → M => iRv (iVFAdd (z 0) (iVFNeg (z 1)))) := by
    have h : B.real.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMap) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 1 Fn.rvMap)
    exact h.comp (fun i => by fin_cases i; exact ha)
  exact (Set.DefinableFun.proj LRV).ofPred_eq hr

theorem pair_graph_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B (PairMapFibres.graph A f (difference (M := M))) := by
  have hd := difference_graph_definable B
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact PairMapFibres.graph_definable hp hf hd

end IntegrationInACVF.Section3ACVF.RVDifferencePairs
