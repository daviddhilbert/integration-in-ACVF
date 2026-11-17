module

public import Integration7.GammaRVLabelIdentity
public import Integration7.RVVolumeComposition
public import Integration7.RVVolumeInverse

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual volume isomorphisms that keep labels fixed inherit the
original-Gamma chart of their essential source domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a k : ℕ}

theorem gamma_volume_iso_label_identity (B : Base (M := M))
    {D E : DefSet (rawRVSpace (M := M) a) S}
    {v : Map D (DefSet.univ (rawRVSpace (M := M) (k+1)) S)}
    {w : Map E (DefSet.univ (rawRVSpace (M := M) (k+1)) S)}
    {hv : v.FiniteFibres} {hw : w.FiniteFibres}
    {ω : VolumeForm D} {π : VolumeForm E}
    (e : RVVolumeIso
      (⟨⟨⟨a,D,v⟩,hv⟩,ω⟩ : PositiveRVVolumeObject (M := M) S k)
      (⟨⟨⟨a,E,w⟩,hw⟩,π⟩ : PositiveRVVolumeObject (M := M) S k))
    (hD : GammaSetDefinable B {p : Point (M := M) 0 a |
      p.2 ∈ (⟨⟨⟨a,D,v⟩,hv⟩,ω⟩ : PositiveRVVolumeObject (M := M) S k).essential.obj.domain.carrier})
    (hMap : ∀ u, (finiteIsoMap e.iso u).val = u.val) : e.GammaDefinable B := by
  apply GammaGraphDefinable.congr (gamma_rv_restricted_label_identity B _ hD)
  intro p q
  constructor
  · rintro ⟨hp,hq⟩
    exact ⟨⟨p.2,hp⟩,rfl,(hMap ⟨p.2,hp⟩).trans hq⟩
  · rintro ⟨u,hu,hq⟩
    have hp : p.2 ∈ (⟨⟨⟨a,D,v⟩,hv⟩,ω⟩ : PositiveRVVolumeObject (M := M) S k).essential.obj.domain.carrier :=
      hu ▸ u.property
    exact ⟨hp,hu.symm.trans ((hMap u).symm.trans hq)⟩

end IntegrationInACVF.Section7
