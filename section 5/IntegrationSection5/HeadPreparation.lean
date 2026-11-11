import IntegrationSection5.RelativeFibreBijection
import IntegrationSection5.HeadContractionGeometry

/-! An actual stage of the ordered contraction construction. This data
structure includes the preparation and is not an existence assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

structure HeadPreparation (A : DefSet (M := M) S (n+1) m) where
  arity : ℕ
  target : DefSet (M := M) S (n+1) arity
  map : Map A target
  special : SpecialRelative map 0
  saturated : HeadSaturated (carrier target)

namespace HeadPreparation
variable {A : DefSet (M := M) S (n+1) m}

theorem bijective (T : HeadPreparation A) : Function.Bijective T.map :=
  specialRelative_bijective T.special

def contractedSet (T : HeadPreparation A) := headImage T.target

def contractionMap (T : HeadPreparation A) : Map A T.contractedSet :=
  Map.comp (Map.toImage (headKeyMap T.target)) T.map

def liftSet (T : HeadPreparation A) := coordinateCanonicalImage T.target 0

def liftMap (T : HeadPreparation A) : Map A T.liftSet :=
  Map.comp (coordinateCanonicalBijection T.target 0) T.map

theorem liftMap_bijective (T : HeadPreparation A) : Function.Bijective T.liftMap :=
  (coordinateCanonicalBijection_bijective T.target 0).comp T.bijective

theorem contractionMap_surjective (T : HeadPreparation A) : Function.Surjective T.contractionMap := by
  rintro ⟨q,b,hb⟩
  obtain ⟨a,ha⟩ := T.bijective.2 b
  refine ⟨a,Subtype.ext ?_⟩
  change (headKeyMap T.target (T.map a)).val = q
  rw [ha]
  exact hb

theorem lifting_square (T : HeadPreparation A) (a : A) :
    dropHead id (T.liftMap a).val = (T.contractionMap a).val := by
  exact (headKeyMap_apply T.target (T.map a)).symm

theorem liftSet_exact (T : HeadPreparation A) (q : Point (M := M) (n+1) (1+T.arity)) :
    q ∈ carrier T.liftSet ↔ dropHead id q ∈ carrier T.contractedSet ∧
      q.2 (Fin.castAdd T.arity 0) = rv (vfAt q 0) :=
  coordinateCanonical_image_headLift T.target T.saturated q

theorem contractionMap_eq_iff (T : HeadPreparation A) (a b : A) :
    T.contractionMap a = T.contractionMap b ↔
      TailEq (T.map a).val (T.map b).val ∧ SameRV (T.map a).val (T.map b).val := by
  rw [Subtype.ext_iff]
  change (headKeyMap T.target (T.map a)).val = (headKeyMap T.target (T.map b)).val ↔ _
  rw [headKeyMap_apply,headKeyMap_apply]
  exact headKey_eq_iff _ _

end HeadPreparation
end IntegrationInACVF.Section5
