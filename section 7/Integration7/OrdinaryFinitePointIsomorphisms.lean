module

public import Integration7.GammaIndexedOrdinaryCoordinateIsomorphisms
public import IntegrationSection6.FiniteGammaIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A Gamma bijection of ordinary finite point domains is an actual
finite RV[0] isomorphism. Its empty volume tuple has constant weight. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}
variable {D : Set (Fin a → RV (M := M))} {E : Set (Fin b → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin 0 → RV (M := M)) → Prop}
variable {S : (Fin b → RV (M := M)) → (Fin 0 → RV (M := M)) → Prop}
variable (P : GammaFiniteGraphPresentation B a 0 D R) (Q : GammaFiniteGraphPresentation B b 0 E S)
variable (e : GammaIso B {p : Point (M := M) 0 a | p.2 ∈ D} {q : Point (M := M) 0 b | q.2 ∈ E})

def ordinaryFinitePointLabelEquiv : P.domain ≃ Q.domain :=
  (Set.equivOfEq P.domain_eq).trans ((pureRVLabelPointEquiv D).trans
    (e.equiv.trans ((pureRVLabelPointEquiv E).symm.trans (Set.equivOfEq Q.domain_eq).symm)))

def ordinaryFinitePointGammaIso : GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let f := ordinaryFinitePointLabelEquiv P Q e
  apply FiniteRV.gammaIsoOfFiniteEquiv P.toGamma Q.toGamma f
  · apply GammaGraphDefinable.congr e.graph
    intro p q
    constructor
    · rintro ⟨u,hu,hv⟩
      let x : P.domain := ⟨u.val.2,(Set.ext_iff.mp P.domain_eq u.val.2).mpr u.property⟩
      have hx : (pureRVLabelPointEquiv D) ((Set.equivOfEq P.domain_eq) x) = u :=
        Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
      refine ⟨x,congrArg (fun z : Point (M := M) 0 a => z.2) hu,?_⟩
      change (e.equiv ((pureRVLabelPointEquiv D) ((Set.equivOfEq P.domain_eq) x))).val.2 = q.2
      exact (congrArg (fun z => (e.equiv z).val.2) hx).trans
        (congrArg (fun z : Point (M := M) 0 b => z.2) hv)
    · rintro ⟨u,hu,hv⟩
      exact ⟨(pureRVLabelPointEquiv D) ((Set.equivOfEq P.domain_eq) u),
        Prod.ext (Subsingleton.elim _ _) hu,Prod.ext (Subsingleton.elim _ _) hv⟩
  · intro u
    exact congrArg (fun t : Fin 0 → M => rawWeight t) (Subsingleton.elim _ _)

end IntegrationInACVF.Section7
