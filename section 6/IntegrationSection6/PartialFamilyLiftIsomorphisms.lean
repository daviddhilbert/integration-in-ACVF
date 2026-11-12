import IntegrationSection6.PartialContractionFamilies
import IntegrationSection6.ActiveFrozenShuffle
import IntegrationSection6.DefinableFamilyLifts

/-! The relative partial-contraction representative lifts to the original
mixed family by an actual original-base Gamma isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p n a l : ℕ}
variable {U : DefSet (M := M) S (p+n) a} {V : DefSet (M := M) S p l}

theorem partialContractionSchema_liftCondition (A : Set (Point (M := M) p 0))
    (T : PartialContractionProgram S p (n := n) U V) (hT : GammaPartialProgramDefinable B T)
    (hUA : ∀ u : U, (fun j => vfAt u.val (frozenIndex p n j),Fin.elim0) ∈ A)
    (q : Point (M := M) (p+n) l) :
    q ∈ familyLiftDomain A (partialContractionSchema T hT) ↔
      T.LiftCondition (q.1 ∘ activeFrozenShuffle p n,q.2) := by
  change ((q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A ∧
    (coordinateRVFamilySchema (carrier V) (gamma_partial_program_final_set T hT) T.volumeIndex).rowVolume
      (fun j => (q.1 (Fin.castAdd n j)).val) q.2 (tupleRV (q.1 ∘ Fin.natAdd p))) ↔ _
  rw [coordinateRVFamilySchema_volume]
  constructor
  · rintro ⟨_,hD,hvol⟩
    refine ⟨⟨(q.1 ∘ Fin.castAdd n,q.2),hD⟩,rfl,?_,?_⟩
    · intro j
      change q.1 (Fin.castAdd n j) = q.1 (activeFrozenShuffle p n (frozenIndex p n j))
      rw [activeFrozenShuffle_frozen]
    · intro i
      change q.2 (T.volumeIndex i) = rv (q.1 (activeFrozenShuffle p n (activeIndex p n i)))
      rw [activeFrozenShuffle_active]
      exact congrFun hvol i
  · rintro ⟨u,hu,hf,hv⟩
    have hfirst : u.val.1 = q.1 ∘ Fin.castAdd n := by
      funext j
      have h := hf j
      change u.val.1 j = q.1 (activeFrozenShuffle p n (frozenIndex p n j)) at h
      rwa [activeFrozenShuffle_frozen] at h
    have hpoint : u.val = (q.1 ∘ Fin.castAdd n,q.2) := Prod.ext hfirst hu
    refine ⟨?_,hpoint ▸ u.property,?_⟩
    · have h := partialContraction_target_base A T hUA u
      exact (congrArg (fun f : Fin p → VF (M := M) => (f,Fin.elim0)) hfirst) ▸ h
    · funext i
      have h := hv i
      change u.val.2 (T.volumeIndex i) = rv (q.1 (activeFrozenShuffle p n (activeIndex p n i))) at h
      rw [activeFrozenShuffle_active] at h
      exact (congrFun hu (T.volumeIndex i)).symm.trans h

def gammaPartialFamilyLiftIso (hBS : B.real ⊆ S) (hU : GammaSetDefinable B (carrier U))
    (A : Set (Point (M := M) p 0)) (T : PartialContractionProgram S p (n := n) U V)
    (hT : GammaPartialProgramDefinable B T)
    (hUA : ∀ u : U, (fun j => vfAt u.val (frozenIndex p n j),Fin.elim0) ∈ A) :
    GammaIso B (carrier U) (familyLiftDomain A (partialContractionSchema T hT)) := by
  let e := gammaPartialNaturalIso hBS T hT
  let hD := e.target_definable (gammaLogicInput B)
  let f := gammaVFCoordinateIso (carrier T.naturalImage) hD (activeFrozenShuffle p n).symm
  have hset : {q : Point (M := M) (p+n) l |
      (q.1 ∘ (activeFrozenShuffle p n).symm.symm,q.2) ∈ carrier T.naturalImage} =
        familyLiftDomain A (partialContractionSchema T hT) := by
    ext q
    rw [Equiv.symm_symm]
    exact (T.naturalImage_exact (q.1 ∘ activeFrozenShuffle p n,q.2)).trans
      (partialContractionSchema_liftCondition A T hT hUA q).symm
  exact (e.trans (gammaLogicInput B) f).congr rfl hset

end IntegrationInACVF.Section6
