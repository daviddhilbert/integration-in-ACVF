module

public import Integration7.GammaRVMapGraphOperations
public import Integration7.ScalarRVAlgebra
public import Integration7.RVUnitNormalization
public import Integration7.RVCoordinateSelection

@[expose] public section

/-! Scalar RV arithmetic and unit normalization preserve the full
original-Gamma graph of their inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput PresentedSet pointSpace carrier setDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b c : ℕ}

private theorem gamma_univ_rv_source (B : Base (M := M)) (a : ℕ) (S : Set M) :
    GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ (DefSet.univ (rawRVSpace (M := M) a) S).carrier} := by
  let P := PresentedSet.univ (pointSpace (M := M) 0 a) B.real
  exact (gammaLogicInput B).real_set (carrier P) (setDefinable P)

theorem RVMapGamma.select
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S}
    {f : Map A (DefSet.univ (rawRVSpace (M := M) b) S)}
    (hf : RVMapGamma f B) (σ : Fin c → Fin b) :
    RVMapGamma ((rvCoordinateSelectMap S σ).comp f) B := by
  have hΓ := gamma_real_rv_map_graph hc B (rvCoordinateSelectMap S σ)
    (rvCoordinateSelectMap B.real σ) (gamma_univ_rv_source B b S) (fun _ => rfl)
  exact hf.comp hΓ

theorem RVMapGamma.inverseScalar
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S}
    {f : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)}
    (hf : RVMapGamma f B) : RVMapGamma ((rvInverse S).comp f) B := by
  have hΓ := gamma_real_rv_map_graph hc B (rvInverse S) (rvInverse B.real)
    (gamma_univ_rv_source B 1 S) (fun _ => rfl)
  exact hf.comp hΓ

theorem RVMapGamma.unitNormalize
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S}
    {f : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)}
    (hf : RVMapGamma f B) : RVMapGamma ((rvUnitNormalize S).comp f) B := by
  have hΓ := gamma_real_rv_map_graph hc B (rvUnitNormalize S) (rvUnitNormalize B.real)
    (gamma_univ_rv_source B 1 S) (fun _ => rfl)
  exact hf.comp hΓ

private def rvTupleMultiply (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) (1+1)) S) (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  (rvMultiply S).comp (((rvCoordinateSelectMap S (fun _ : Fin 1 => Fin.castAdd 1 (0 : Fin 1))).pair
    (rvCoordinateSelectMap S (fun _ : Fin 1 => Fin.natAdd 1 (0 : Fin 1)))).toUniv)

theorem RVMapGamma.scalarMul
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S}
    {f g : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)}
    (hf : RVMapGamma f B) (hg : RVMapGamma g B) : RVMapGamma (rvScalarMul f g) B := by
  have hΓ := gamma_real_rv_map_graph hc B (rvTupleMultiply S) (rvTupleMultiply B.real)
    (gamma_univ_rv_source B (1+1) S) (fun _ => rfl)
  apply ((hf.append hg).comp hΓ).congr
  intro u
  funext i
  fin_cases i
  rfl

theorem RVMapGamma.scalarOne
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) a) S)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier}) :
    RVMapGamma (rvScalarOne A) B :=
  gamma_real_rv_map_graph hc B (rvScalarOne A)
    (rvScalarOne (DefSet.univ (rawRVSpace (M := M) a) B.real)) hA (fun _ => rfl)

end IntegrationInACVF.Section7
