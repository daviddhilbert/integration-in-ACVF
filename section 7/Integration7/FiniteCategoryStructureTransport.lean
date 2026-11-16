module

public import Integration7.VFVolumeObjects
public import Integration7.CanonicalFiniteRVObjects

@[expose] public section

/-! Transport the existing finite VF and RV categories along literal
equality of their shared language structures. This only changes the
presentation and supplies compatibility with the ordinary lift. -/
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} {I J : LRV.Structure M}

def vfFiniteStructureEquiv (h : I = J) (S : Set M) (n : ℕ) :
    @VFFiniteObject M I (@rawRVSpace M I 1) S n ≌ @VFFiniteObject M J (@rawRVSpace M J 1) S n := by
  cases h
  exact CategoryTheory.Equivalence.refl

def rvFiniteStructureEquiv (h : I = J) (S : Set M) (n : ℕ) :
    @RVFiniteObject M I S n ≌ @RVFiniteObject M J S n := by
  cases h
  exact CategoryTheory.Equivalence.refl

theorem finite_structure_transport_lift (h : I = J)
    (hI : @Theory.Model LRV M I Axioms.ACVF) (hJ : @Theory.Model LRV M J Axioms.ACVF)
    {S : Set M} {n : ℕ} (U : @RVFiniteObject M I S n) :
    (vfFiniteStructureEquiv h S n).functor.obj (@rvLiftFiniteObject M I hI S n (@rawRVSpace M I 1) U) =
      @rvLiftFiniteObject M J hJ S n (@rawRVSpace M J 1) ((rvFiniteStructureEquiv h S n).functor.obj U) := by
  cases h
  rfl

end IntegrationInACVF.Section7
