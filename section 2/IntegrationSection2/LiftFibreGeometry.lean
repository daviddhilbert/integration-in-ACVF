import Section4.LiftFibres
import Section7.GammaPolynomial

/-! A fixed actual RV label has exactly the expected VF polydisc.
All tuple and leading-term comparisons use the released RV quotient. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section2.LiftFibreGeometry

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
  [LinearOrderedCommGroupWithZero Γ] {S T : Set M} {k : ℕ}

theorem nonzero_representatives (t : Fin k → CanonicalRV.RVSort M)
    (ht : ∀ i, (t i).val ≠ iRVZero) :
    ∃ a : Fin k → VFType (M := M), (∀ i, a i ≠ 0) ∧ tupleRV a = t := by
  obtain ⟨a,ha⟩ := tupleRV_surjective t
  refine ⟨a,fun i hi => ht i ?_,ha⟩
  have he : CanonicalRV.encodedRv (a i) = t i := congrFun ha i
  exact (congrArg Subtype.val he).symm.trans ((CanonicalRV.encodedRv_zero_iff (a i)).mpr hi)

theorem projection (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (U : RVObject (M := M) S k) (u : U.domain)
    (hST : S ∪ Set.range (rvValues u.val) ⊆ T)
    (a : Fin k → VFType (M := M)) (ha : tupleRV a = U.value u)
    (x : Fin k → VFType (M := M)) :
    (∃ p : (liftFibre U u).extend hST, p.val.1 = x) ↔
      x ∈ RVFibre v (fun i => RVCalc.rv v (a i)) := by
  constructor
  · rintro ⟨p,rfl⟩ i
    have hp := (mem_liftFibre U u p.val).mp p.property
    apply (CanonicalRV.same_fibers v hv _ _).mpr
    exact congrFun (hp.1.trans ha.symm) i
  · intro hx
    have he : tupleRV x = U.value u := by
      apply Eq.trans _ ha
      funext i
      exact (CanonicalRV.same_fibers v hv _ _).mp (hx i)
    exact ⟨⟨(x,u.val),(mem_liftFibre U u _).mpr ⟨he,rfl⟩⟩,rfl⟩

end IntegrationInACVF.Section2.LiftFibreGeometry
