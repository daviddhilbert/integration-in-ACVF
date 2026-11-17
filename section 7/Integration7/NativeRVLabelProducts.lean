module

public import Integration7.NativeVolumeMapRealization
public import Integration7.RVCoordinateSelection
public import Integration7.ScalarRVAlgebra

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Multiplication of literal RV labels is an actual pure-RV native map
over the original parameter set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.realSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}

def nativeRVLabelProduct (hc : CanonicalStructure.IsCanonical (M := M))
    (Q : SpecialTransformations.Section5.DefSet (M := M) S 0 a) (ι κ : Fin a) :
    SpecialTransformations.Section5.Map Q
      (SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) 0 1) S) := by
  let A := rawSpecialSet hc Q
  let labels := Map.snd (rawVFSpace (M := M) 0) (rawRVSpace a) S A
  let f := (rvCoordinateSelectMap S (fun _ : Fin 1 => ι)).comp labels
  let g := (rvCoordinateSelectMap S (fun _ : Fin 1 => κ)).comp labels
  let h := (Map.fst (rawVFSpace (M := M) 0) (rawRVSpace a) S A).pair (rvScalarMul f g)
  let hn := nativeMixedVolumeMap hc h
  let j : SpecialTransformations.Section5.Map Q (nativeMixedVolumeDomain hc A) :=
    SpecialTransformations.Section5.Map.inclusion (fun _ hp => hp)
  let out : SpecialTransformations.Section5.Map (nativeMixedVolumeDomain hc
      ((DefSet.univ (rawVFSpace (M := M) 0) S).prod (DefSet.univ (rawRVSpace (M := M) 1) S)))
      (SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) 0 1) S) :=
    SpecialTransformations.Section5.Map.inclusion (fun _ _ => Set.mem_univ _)
  exact SpecialTransformations.Section5.Map.comp out (SpecialTransformations.Section5.Map.comp hn j)

theorem native_rv_label_product_value (hc : CanonicalStructure.IsCanonical (M := M))
    (Q : SpecialTransformations.Section5.DefSet (M := M) S 0 a) (ι κ : Fin a) (q : Q) :
    ((nativeRVLabelProduct hc Q ι κ q).val.2 0).val =
      iRVMul (q.val.2 ι).val (q.val.2 κ).val :=
  RVOperations.mul_val (q.val.2 ι : CanonicalRV.RVSort M) (q.val.2 κ : CanonicalRV.RVSort M)
end IntegrationInACVF.Section7
