import Integration7.GammaTermClosureRVMaps
import Integration7.FiniteVolumeIsoMaps
import Section5.GammaLift

/-! Actual bijective RV maps with full Gamma graphs give isomorphisms
of their pure-RV point domains, without naming representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaIso GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {a b : ℕ}

def rvMapPointEquiv {A : DefSet (rawRVSpace (M := M) a) S}
    {D : DefSet (rawRVSpace (M := M) b) S} (g : Map A D) (hg : Function.Bijective g) :
    {p : Point (M := M) 0 a | p.2 ∈ A.carrier} ≃
      {q : Point (M := M) 0 b | q.2 ∈ D.carrier} where
  toFun p := ⟨(Fin.elim0,(g ⟨p.val.2,p.property⟩).val),(g ⟨p.val.2,p.property⟩).property⟩
  invFun q := ⟨(Fin.elim0,(g.inverse hg ⟨q.val.2,q.property⟩).val),
    (g.inverse hg ⟨q.val.2,q.property⟩).property⟩
  left_inv p := Subtype.ext (Prod.ext (Subsingleton.elim _ _)
    (congrArg Subtype.val (Map.inverse_apply g hg ⟨p.val.2,p.property⟩)))
  right_inv q := Subtype.ext (Prod.ext (Subsingleton.elim _ _)
    (congrArg Subtype.val (Map.apply_inverse g hg ⟨q.val.2,q.property⟩)))

def rvMapGammaPointIso {A : DefSet (rawRVSpace (M := M) a) S}
    {D : DefSet (rawRVSpace (M := M) b) S} (g : Map A D) (hg : Function.Bijective g)
    (hΓ : RVMapGamma g B) :
    GammaIso B {p : Point (M := M) 0 a | p.2 ∈ A.carrier}
      {q : Point (M := M) 0 b | q.2 ∈ D.carrier} where
  equiv := rvMapPointEquiv g hg
  graph := GammaGraphDefinable.congr hΓ (by
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨(Fin.elim0,u.val),u.property⟩,Prod.ext (Subsingleton.elim _ _) hu,
        Prod.ext (Subsingleton.elim _ _) hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val.2,u.property⟩,congrArg Prod.snd hu,congrArg Prod.snd hq⟩)

end IntegrationInACVF.Section7
