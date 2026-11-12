import IntegrationSection6.GammaVFCoordinateIsomorphisms
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fin.Basic

/-! Arbitrary coordinate projections, including every subset of the VF
coordinates, with explicit retained/complementary enumerations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6

structure VFCoordinateProjection (n p : ℕ) where
  discarded : ℕ
  split : Fin (p+discarded) ≃ Fin n

def VFCoordinateProjection.retainedIndex {n p : ℕ} (E : VFCoordinateProjection n p) : Fin p → Fin n :=
  E.split ∘ Fin.castAdd E.discarded

def VFCoordinateProjection.ofSet {n : ℕ} (E : Set (Fin n)) : VFCoordinateProjection n (Fintype.card E) where
  discarded := Fintype.card (Eᶜ : Set (Fin n))
  split := finSumFinEquiv.symm.trans ((Equiv.sumCongr (Fintype.equivFin E).symm
    (Fintype.equivFin (Eᶜ : Set (Fin n))).symm).trans (Equiv.Set.sumCompl E))

theorem VFCoordinateProjection.ofSet_retained {n : ℕ} (E : Set (Fin n)) (j : Fin (Fintype.card E)) :
    (VFCoordinateProjection.ofSet E).retainedIndex j = ((Fintype.equivFin E).symm j).val := by
  simp only [VFCoordinateProjection.retainedIndex,Function.comp_apply,VFCoordinateProjection.ofSet,
    Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,Equiv.sumCongr_apply,Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl]

theorem VFCoordinateProjection.ofSet_range {n : ℕ} (E : Set (Fin n)) :
    Set.range (VFCoordinateProjection.ofSet E).retainedIndex = E := by
  ext i
  constructor
  · rintro ⟨j,rfl⟩
    rw [VFCoordinateProjection.ofSet_retained]
    exact ((Fintype.equivFin E).symm j).property
  · intro hi
    refine ⟨(Fintype.equivFin E) ⟨i,hi⟩,?_⟩
    rw [VFCoordinateProjection.ofSet_retained]
    rw [Equiv.symm_apply_apply]

def finAppendEquiv {r n : ℕ} (e : Fin r ≃ Fin n) (k : ℕ) : Fin (r+k) ≃ Fin (n+k) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin k))).trans finSumFinEquiv)

theorem finAppendEquiv_left {r n : ℕ} (e : Fin r ≃ Fin n) (k : ℕ) (j : Fin r) :
    finAppendEquiv e k (Fin.castAdd k j) = Fin.castAdd k (e j) := by
  simp only [finAppendEquiv,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply,Sum.map_inl,finSumFinEquiv_apply_left]

theorem finAppendEquiv_right {r n : ℕ} (e : Fin r ≃ Fin n) (k : ℕ) (j : Fin k) :
    finAppendEquiv e k (Fin.natAdd r j) = Fin.natAdd n j := by
  simp only [finAppendEquiv,Equiv.trans_apply,finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply,Sum.map_inr,Equiv.refl_apply,finSumFinEquiv_apply_right]

def VFCoordinateProjection.liftSplit {n p : ℕ} (E : VFCoordinateProjection n p) (k : ℕ) :
    Fin (p+(E.discarded+k)) ≃ Fin (n+k) :=
  (finCongr (Nat.add_assoc p E.discarded k).symm).trans (finAppendEquiv E.split k)

theorem VFCoordinateProjection.liftSplit_prefix {n p : ℕ} (E : VFCoordinateProjection n p)
    (k : ℕ) (j : Fin p) :
    E.liftSplit k (Fin.castAdd (E.discarded+k) j) = Fin.castAdd k (E.retainedIndex j) := by
  have hi : Fin.cast (Nat.add_assoc p E.discarded k).symm (Fin.castAdd (E.discarded+k) j) =
      Fin.castAdd k (Fin.castAdd E.discarded j) := Fin.ext rfl
  change finAppendEquiv E.split k (Fin.cast (Nat.add_assoc p E.discarded k).symm _) = _
  rw [hi,finAppendEquiv_left]
  rfl

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n p : ℕ}

def VFCoordinateProjection.baseImage (E : VFCoordinateProjection n p) (A : Set (Point (M := M) n 0)) :
    Set (Point (M := M) p 0) := {q | ∃ x : A, (x.val.1 ∘ E.retainedIndex,Fin.elim0) = q}

theorem VFCoordinateProjection.gamma_baseImage (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) :
    GammaSetDefinable B (E.baseImage A) := by
  let f := mixedCoordinatePointMap E.retainedIndex (Fin.elim0 : Fin 0 → Fin 0) B.real
  have h := (gammaLogicInput B).image_real f hA
  convert h using 1
  ext q
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨⟨x.val,Set.mem_univ _⟩,x.property,?_⟩
    have he : (f ⟨x.val,Set.mem_univ _⟩).val = (x.val.1 ∘ E.retainedIndex,Fin.elim0) :=
      Prod.ext rfl (funext (fun j => j.elim0))
    exact he.trans hx
  · rintro ⟨x,hx,he⟩
    refine ⟨⟨x.val,hx⟩,?_⟩
    have hf : (f x).val = (x.val.1 ∘ E.retainedIndex,Fin.elim0) := Prod.ext rfl (funext (fun j => j.elim0))
    exact hf.symm.trans he

end IntegrationInACVF.Section6
