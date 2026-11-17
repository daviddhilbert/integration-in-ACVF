module

public import Integration7.StabilizedVolumeCoordinateIsomorphisms
public import Integration7.NormalizedBasicVolumePresentation
public import Integration7.VolumeClassCoordinatePermutations
public import Mathlib.Logic.Equiv.Fin.Basic

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every unsigned volume-coordinate permutation becomes invisible in
the actual normalized coefficient ring. The proof first gives a full
volume isomorphism after multiplying by the point, then uses point=1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def pointExtendedVolumePermutation (σ : Equiv.Perm (Fin (k+1))) :
    Equiv.Perm (Fin ((k+1)+1)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr σ (Equiv.refl (Fin 1)))).trans finSumFinEquiv

def volumePointPermutationProductIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    RVVolumeIso
      ((U.prod (degreeOnePointVolumeObject (C.base : Set M))).permuteVolume (pointExtendedVolumePermutation σ))
      ((U.permuteVolume σ).prod (degreeOnePointVolumeObject (C.base : Set M))) := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  let A := (U.prod P).permuteVolume (pointExtendedVolumePermutation σ)
  let B := (U.permuteVolume σ).prod P
  let f : Map A.underlying.obj.domain B.underlying.obj.domain := Map.id _
  have hcoord (q : A.underlying.obj.domain) : B.underlying.obj.value (f q) = A.underlying.obj.value q := by
    obtain ⟨u,p,rfl⟩ := exists_rvPackPair U.underlying.obj.domain P.underlying.obj.domain q
    change ((U.permuteVolume σ).prod P).underlying.obj.value (rvPackPair _ _ u p) =
      (U.prod P).underlying.obj.value (rvPackPair _ _ u p) ∘ pointExtendedVolumePermutation σ
    rw [positiveProduct_coordinates_pair,positiveProduct_coordinates_pair]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [rvAppend,Fin.append_left,Function.comp_apply,pointExtendedVolumePermutation,
        Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,Equiv.sumCongr_apply,Sum.map_inl,finSumFinEquiv_apply_left]
      rfl
    · simp only [rvAppend,Fin.append_right,Function.comp_apply,pointExtendedVolumePermutation,
        Equiv.trans_apply,finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Sum.map_inr,Equiv.refl_apply,finSumFinEquiv_apply_right]
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f Function.bijective_id hcoord)) hcoord (fun _ => rfl)

def pointStabilizedVolumeCoordinateIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    RVVolumeIso (U.prod (degreeOnePointVolumeObject (C.base : Set M)))
      ((U.permuteVolume σ).prod (degreeOnePointVolumeObject (C.base : Set M))) :=
  (pointStabilizedVolumePermutationIso C U (pointExtendedVolumePermutation σ)).trans hc C
    (volumePointPermutationProductIso hc C U σ)

theorem normalized_basic_volume_coordinate_invariance
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := k+1) U) =
      normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := k+1) (U.permuteVolume σ)) := by
  have h := congrArg (normalizedBasicVolumeMap hc C)
    (volume_iso_semiring_class_iso hc C (pointStabilizedVolumeCoordinateIso hc C U σ))
  rw [volume_iso_semiring_class_positive_product,volume_iso_semiring_class_positive_product,
    map_mul,map_mul,normalized_basic_volume_point,mul_one,mul_one] at h
  exact h

theorem normalized_basic_volume_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C U) =
      normalizedVolumeCoefficientMap hc C
        (DirectSum.of (RVVolumeBlowupClasses hc C) n (rvVolumeBlowupClass hc C U)) := by
  change normalizedVolumeCoefficientMap hc C (rvVolumeGradedBlowupProjection hc C
    (DirectSum.of (RVVolumeIsoClasses hc C) n (rvVolumeIsoClass hc C U))) = _
  rw [rvVolumeGradedBlowupProjection_of]
  rfl

set_option maxHeartbeats 1200000 in
theorem normalized_volume_coordinate_invariance
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (k+1))) (a : PositiveVolumeBlowupClasses hc C k) :
    normalizedVolumeCoefficientMap hc C
      (DirectSum.of (RVVolumeBlowupClasses hc C) (k+1) a) =
    normalizedVolumeCoefficientMap hc C
      (DirectSum.of (RVVolumeBlowupClasses hc C) (k+1) (positiveVolumeClassPermute hc C σ a)) := by
  induction a using Quotient.inductionOn with
  | h U =>
    exact (normalized_basic_volume_class hc C (n := k+1) U).symm.trans
      ((normalized_basic_volume_coordinate_invariance hc C (k := k) U σ).trans
        (normalized_basic_volume_class hc C (n := k+1) (U.permuteVolume σ)))

end IntegrationInACVF.Section7
