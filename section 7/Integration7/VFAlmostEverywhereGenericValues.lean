import Integration7.VFAlmostEverywhere
import Section9.MixedDifferentiationAE

/-! A definable VF-small exception contains no point whose full VF tuple
is algebraically independent over the original real parameter field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

theorem VFAlmostEverywhere.at_independent
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S} {P : A → Prop}
    (h : VFAlmostEverywhere A P) (p : A)
    (hp : AlgebraicIndependent (vfParameterField S) p.val.1) : P p := by
  obtain ⟨D,hDA,hD,hP⟩ := h
  apply hP p
  intro hmem
  let q : D := ⟨p.val,hmem⟩
  have hRank : vfTupleTrdeg S q.val.1 = (n : ℕ) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) q.val.1).mpr hp
  have hle := vfTupleTrdeg_le_vfDim hc (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) D q
  rw [hRank] at hle
  have hn : n ≤ vfDim (rawRVSpace (M := M) 1) D := by exact_mod_cast hle
  exact Nat.not_le_of_lt hD hn

end IntegrationInACVF.Section7
