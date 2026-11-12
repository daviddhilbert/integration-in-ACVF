import IntegrationSection6.GammaGraphPresentationIsomorphisms
import IntegrationSection6.FiniteGammaObjects

/-! Extend finite graph presentations to a common internal finite-code
base. Original-Gamma domain and volume certificates are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}

def GammaFiniteGraphPresentation.extend (P : GammaFiniteGraphPresentation B a k D R)
    (T : Set M) (hPT : P.codes ⊆ T) (hT : ∃ E : Set M, E.Finite ∧ T = B.real ∪ E) :
    GammaFiniteGraphPresentation B a k D R := by
  let A := FiniteRV.gammaObjectAtExtend P.toGamma hPT
  exact {
    codes := T
    real_contains := A.real_contains
    finite_extra := hT
    domain := @rvObjectDomain M sM T k A.object.obj
    domain_eq := P.domain_eq
    volume := @rvObjectVolume M sM T k A.object.obj
    graph_iff := P.graph_iff
    finite_volume := A.object.property
    domain_graph := P.domain_graph
    volume_graph := A.volume_graph }

theorem GammaFiniteGraphPresentation.union_finite_extra
    (P : GammaFiniteGraphPresentation B a k D R)
    {E : Set (Fin b → RV (M := M))}
    {S : (Fin b → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
    (Q : GammaFiniteGraphPresentation B b k E S) :
    ∃ H : Set M, H.Finite ∧ P.codes ∪ Q.codes = B.real ∪ H := by
  obtain ⟨H,hH,hP⟩ := P.finite_extra
  obtain ⟨J,hJ,hQ⟩ := Q.finite_extra
  refine ⟨H ∪ J,hH.union hJ,?_⟩
  rw [hP,hQ]
  apply Set.ext
  intro x
  simp only [Set.mem_union]
  tauto

end IntegrationInACVF.Section6
