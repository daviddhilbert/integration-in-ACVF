module

public import Integration7.CanonicalVolumePresentations
public import IntegrationSection6.GammaRVGlobalRestriction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An explicit global real RV formula, restricted to an original-Gamma
domain, has its full graph over that same Gamma base. Canonical raw maps
are transported to the existing normalized graph theorem without changing
their values or naming extra parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

private def normalizedRVDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) a) S) : @DefSet LRV M N (@rawRVSpace M N a) S := by
  let T := @Space.preimage LRV M sM (@rawRVSpace M sM a) A.carrier
  have h : @Set.Definable M S LRV N (Fin a) T :=
    Eq.mp (congrArg (fun I : LRV.Structure M => @Set.Definable M S LRV I (Fin a) T)
      (normalize_eq_of_isCanonical hc).symm) A.definable
  exact @DefSet.mk LRV M N (@rawRVSpace M N a) S A.carrier h

private def normalizedRVMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A B) : @Map LRV M N _ _ S (normalizedRVDomain hc A) (normalizedRVDomain hc B) := by
  let T := @Space.relation LRV M sM (@rawRVSpace M sM a) (@rawRVSpace M sM b)
    (fun x y => ∃ u : A, u.val = x ∧ (f u).val = y)
  have h : @Set.Definable M S LRV N (Fin a ⊕ Fin b) T :=
    Eq.mp (congrArg (fun I : LRV.Structure M => @Set.Definable M S LRV I (Fin a ⊕ Fin b) T)
      (normalize_eq_of_isCanonical hc).symm) f.graph_definable
  exact @Map.mk LRV M N _ _ S (normalizedRVDomain hc A) (normalizedRVDomain hc B)
    (fun x => ⟨(f ⟨x.val,x.property⟩).val,(f ⟨x.val,x.property⟩).property⟩) h

theorem gamma_real_rv_map_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A D)
    (g : Map (DefSet.univ (rawRVSpace (M := M) a) B.real)
      (DefSet.univ (rawRVSpace (M := M) b) B.real))
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier})
    (hfg : ∀ u : A, (f u).val = (g ⟨u.val,Set.mem_univ _⟩).val) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
      ∃ u : A, u.val = p.2 ∧ (f u).val = q.2) :=
  gamma_rv_graph_of_global_formula (normalizedRVMap hc f) (normalizedRVMap hc g) hA
    (fun u => hfg ⟨u.val,u.property⟩)

end IntegrationInACVF.Section7
