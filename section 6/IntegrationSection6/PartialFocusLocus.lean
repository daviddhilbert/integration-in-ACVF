import IntegrationSection6.LiftLoci
import Section5.ZeroNormalization
import IntegrationSection6.OriginalAdmissibleFocus
import Section3.NormalizationSaturation

/-! The genuine RV-pullback active locus of a partial focus, with the
zero locus removed without changing the transformation. Its label image
is an admissible subobject of the input RV object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

variable {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
variable {i : Fin n} {k : Fin m} (D : Focus A i k)

def focusActiveSet : SpecialTransformations.Section5.DefSet (M := M) S n m :=
  @SpecialTransformations.DefinableGeometry.DefSet.mk LRV M N (@pointSpace M sM hM n m) S
    (carrier A ∩ D.withoutZero.locus)
    (@SpecialTransformations.DefinableGeometry.Space.Definable.inter LRV M N
      (@pointSpace M sM hM n m) S _ _ (setDefinable A) D.withoutZero.locus_definable)

theorem focusActiveSet_subset : carrier (focusActiveSet D) ⊆ carrier A := Set.inter_subset_left

def activeFocus : Focus (focusActiveSet D) i k := D.withoutZero.restrict (focusActiveSet_subset D)

theorem activeFocus_full : carrier (focusActiveSet D) ⊆ (activeFocus D).locus :=
  fun _ hp => ⟨hp.2,subset_hull _ hp⟩

theorem activeFocus_field_nonzero (p : Point (M := M) n m)
    (hp : p ∈ carrier (focusActiveSet D)) : p.1 i ≠ (0 : VF (M := M)) := by
  intro he
  apply D.withoutZero_nonzero p hp.2
  exact (D.tagged p hp.1).trans (congrArg rv he)

theorem activeFocus_eta (p : Point (M := M) n m) (hp : p ∈ carrier (focusActiveSet D)) :
    (activeFocus D).toFocusGeometry.eta p = D.toFocusGeometry.eta p :=
  (D.withoutZero.restrict_eta (focusActiveSet_subset D) p hp).trans (D.withoutZero_eta p hp.1)

include D in
theorem focusActiveSet_pullback (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier (focusActiveSet D)) :=
  isRVPullback_inter hA D.withoutZero.locus_pullback

end IntegrationInACVF.Section6
