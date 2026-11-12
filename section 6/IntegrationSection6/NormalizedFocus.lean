import IntegrationSection6.NormalizedPresentations
import Section5.RootConstruction

/-! A genuine original-model focus is transported to its normalized
presentation. Its locus, centre values and original parameter base are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem rv_normalize (a : VF (M := M)) : @rv M N hN a = rv a := by
  apply Subtype.ext
  exact @CanonicalStructure.normalize_fun M sM 1 Fn.rvMap ![a.val]
    (by intro i; fin_cases i; exact a.property)

theorem vfZero_normalize : @Zero.zero (@VF M N) (@vfInstZero M N hN) = (0 : VF (M := M)) := by
  apply Subtype.ext
  exact @CanonicalStructure.normalize_fun M sM 0 Fn.vfZero Fin.elim0 (fun i => i.elim0)

theorem erase_normalize (p : Point (M := M) n m) (j : Fin n) :
    @erase M N hN n m j p = erase j p := by
  simp only [erase,replace,vfZero_normalize]

theorem key_normalize (p : Point (M := M) n m) :
    @key M N hN n m p = key p := by
  apply Prod.ext
  · funext i
    exact rv_normalize (p.1 i)
  · rfl

theorem hull_normalize (C : Set (Point (M := M) n m)) :
    @hull M N hN n m C = hull C := by
  ext q
  change (∃ p ∈ C, @key M N hN n m p = @key M N hN n m q) ↔
    ∃ p ∈ C, @key M sM hM n m p = @key M sM hM n m q
  constructor
  · rintro ⟨p,hp,he⟩
    exact ⟨p,hp,(@key_normalize M sM hM n m p).symm.trans
      (he.trans (@key_normalize M sM hM n m q))⟩
  · rintro ⟨p,hp,he⟩
    exact ⟨p,hp,(@key_normalize M sM hM n m p).trans
      (he.trans (@key_normalize M sM hM n m q).symm)⟩

theorem pullback_normalize (C : Set (Point (M := M) n m)) :
    @IsRVPullback M N hN n m C ↔ IsRVPullback C := by
  change (@hull M N hN n m C = C) ↔ hull C = C
  rw [hull_normalize]

def normalizedFocusGeometry {C : Set (Point (M := M) n m)} {j : Fin n} {k : Fin m}
    (D : FocusGeometry C j k) : @FocusGeometry M N hN n m C j k := by
  let L := D.locus
  let c := D.center
  refine @FocusGeometry.mk M N hN n m C j k ?_ L ?_ ?_ c ?_ ?_
  · intro p hp
    exact (D.tagged p hp).trans (@rv_normalize M sM hM (p.1 j)).symm
  · exact (pullback_normalize L).mpr D.locus_pullback
  · intro p hp
    change p ∈ @hull M N hN n m C
    rw [hull_normalize]
    exact D.locus_subset hp
  · intro p hp q hq he
    apply D.independent p hp q hq
    exact (@erase_normalize M sM hM n m p j).symm.trans (he.trans (@erase_normalize M sM hM n m q j))
  · intro p hp
    exact D.center_mem p hp

def normalizedFocus {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) : @Focus M N hN S n m (normalizedPointSet A) j k := by
  refine @Focus.mk M N hN S n m (normalizedPointSet A) j k
    (normalizedFocusGeometry D.toFocusGeometry) ?_ ?_
  · let T : Set ((Fin n ⊕ Fin m) → M) :=
      @SpecialTransformations.DefinableGeometry.Space.preimage LRV M N
        (@pointSpace M sM hM n m) D.locus
    have hd : @Set.Definable M S LRV N (Fin n ⊕ Fin m) T := D.locus_definable
    change @Set.Definable M S LRV (@CanonicalStructure.normalize M N) (Fin n ⊕ Fin m) T
    exact Eq.mpr (congrArg (fun s : LRV.Structure M => @Set.Definable M S LRV s (Fin n ⊕ Fin m) T)
      (@normalized_structure_idempotent M sM)) hd
  · let T : Set (((Fin n ⊕ Fin m) ⊕ Fin 1) → M) :=
      @SpecialTransformations.DefinableGeometry.Space.relation LRV M N
        (@pointSpace M sM hM n m) (@SpecialTransformations.Section4.vfSpace M sM hM 1)
        (fun p z => p ∈ carrier A ∩ D.locus ∧ z 0 = D.center p)
    have hd : @Set.Definable M S LRV N ((Fin n ⊕ Fin m) ⊕ Fin 1) T := D.center_graph
    change @Set.Definable M S LRV (@CanonicalStructure.normalize M N) ((Fin n ⊕ Fin m) ⊕ Fin 1) T
    exact Eq.mpr (congrArg (fun s : LRV.Structure M => @Set.Definable M S LRV s ((Fin n ⊕ Fin m) ⊕ Fin 1) T)
      (@normalized_structure_idempotent M sM)) hd


theorem vfSub_normalize (x y : VF (M := M)) :
    (@vfInstAdd M N hN).add x ((@vfInstNeg M N hN).neg y) = x-y := by
  apply Subtype.ext
  change @iVFAdd M N x.val (@iVFNeg M N y.val) = iVFAdd x.val (iVFNeg y.val)
  have hn := @CanonicalStructure.normalize_fun M sM 1 Fn.vfNeg ![y.val]
    (by intro i; fin_cases i; exact y.property)
  change @iVFNeg M N y.val = iVFNeg y.val at hn
  rw [hn]
  exact @CanonicalStructure.normalize_fun M sM 2 Fn.vfAdd ![x.val,iVFNeg y.val]
    (by intro i; fin_cases i; exact x.property; exact vf_neg_mem hM y.property)

theorem focusGeometry_eta_normalize {C : Set (Point (M := M) n m)}
    {j : Fin n} {k : Fin m} (D : FocusGeometry C j k) (p : Point (M := M) n m) :
    @FocusGeometry.eta M N hN n m C j k (normalizedFocusGeometry D) p = D.eta p := by
  dsimp only [normalizedFocusGeometry,FocusGeometry.eta]
  split_ifs
  · apply Prod.ext
    · exact congrArg (Function.update p.1 j) (@vfSub_normalize M sM hM (p.1 j) (D.center p))
    · rfl
  · rfl

@[simp] theorem normalizedFocus_locus {A : DefSet (M := M) S n m}
    {j : Fin n} {k : Fin m} (D : Focus A j k) :
    @FocusGeometry.locus M N hN n m (carrier A) j k
      (@Focus.toFocusGeometry M N hN S n m (normalizedPointSet A) j k (normalizedFocus D)) = D.locus := rfl

@[simp] theorem normalizedFocus_center {A : DefSet (M := M) S n m}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (p : Point (M := M) n m) :
    @FocusGeometry.center M N hN n m (carrier A) j k
      (@Focus.toFocusGeometry M N hN S n m (normalizedPointSet A) j k (normalizedFocus D)) p = D.center p := rfl

end IntegrationInACVF.Section6
