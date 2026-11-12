import IntegrationSection6.GammaFiniteGraphObjects
import IntegrationSection6.FiniteGammaIsomorphisms

/-! Two finite real presentations of the same full original-Gamma domain
and volume relation are canonically isomorphic in RV[k]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}

def gammaGraphPresentationIso (P Q : GammaFiniteGraphPresentation B a k D R) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let e : P.domain ≃ Q.domain := {
    toFun := fun u => ⟨u.val,(Set.ext_iff.mp Q.domain_eq u.val).mpr
      ((Set.ext_iff.mp P.domain_eq u.val).mp u.property)⟩
    invFun := fun v => ⟨v.val,(Set.ext_iff.mp P.domain_eq v.val).mpr
      ((Set.ext_iff.mp Q.domain_eq v.val).mp v.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine FiniteRV.gammaIsoOfFiniteEquiv P.toGamma Q.toGamma e ?_ ?_
  · let L := gammaLogicInput B
    let I := @Map.id M sM _ B.real (PresentedSet.univ (pointSpace (M := M) 0 a) B.real)
    have h := L.restrict_graph P.domain_graph (L.real_map_graph I)
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨hp,z,hz,hq⟩
      have hpq : p = q := hz.symm.trans hq
      let u : P.domain := ⟨p.2,(Set.ext_iff.mp P.domain_eq p.2).mpr hp⟩
      exact ⟨u,rfl,congrArg Prod.snd hpq⟩
    · rintro ⟨u,hu,hq⟩
      have hD : u.val ∈ D := (Set.ext_iff.mp P.domain_eq u.val).mp u.property
      have hpD : p.2 ∈ D := hu ▸ hD
      refine ⟨hpD,⟨p,Set.mem_univ _⟩,rfl,?_⟩
      apply Prod.ext (Subsingleton.elim _ _)
      exact hu.symm.trans hq
  · intro u
    have hQ := (Q.graph_iff (e u).val (Q.volume (e u)).val).mp ⟨e u,rfl,rfl⟩
    obtain ⟨u',hu',hv⟩ := (P.graph_iff u.val (Q.volume (e u)).val).mpr hQ
    have he : u' = u := Subtype.ext hu'
    have hvol : (P.volume u).val = (Q.volume (e u)).val := he ▸ hv
    change rawWeight (fun j => ((P.volume u).val j).val) = rawWeight (fun j => ((Q.volume (e u)).val j).val)
    rw [hvol]

end IntegrationInACVF.Section6
