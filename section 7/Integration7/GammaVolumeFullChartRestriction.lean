module

public import Integration7.GammaEssentialVolumeGraphs

@[expose] public section

/-! A full original-Gamma chart supplies the essential chart of any
actual volume isomorphism agreeing with it on essential labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

theorem gamma_volume_iso_of_full_map
    {U V : PositiveRVVolumeObject (M := M) S k} (e : RVVolumeIso U V)
    (F : Map U.underlying.obj.domain V.underlying.obj.domain)
    (hD : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity |
      p.2 ∈ U.essential.obj.domain.carrier})
    (hF : GammaGraphDefinable B
      (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 V.underlying.obj.arity) =>
        ∃ u : U.underlying.obj.domain, u.val = p.2 ∧ (F u).val = q.2))
    (hMap : ∀ u : U.essential.obj.domain, (finiteIsoMap e.iso u).val =
      (F ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩).val) :
    e.GammaDefinable B := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hD hF)
  intro p q
  constructor
  · rintro ⟨hp,u,hu,hq⟩
    let v : U.essential.obj.domain := ⟨p.2,hp⟩
    have he : (⟨v.val,rvEssentialLabels_subset U.underlying.obj v.property⟩ : U.underlying.obj.domain) = u :=
      Subtype.ext hu.symm
    exact ⟨v,rfl,(hMap v).trans ((congrArg (fun z => (F z).val) he).trans hq)⟩
  · rintro ⟨v,hv,hq⟩
    have hp : p.2 ∈ U.essential.obj.domain.carrier := hv ▸ v.property
    exact ⟨hp,⟨v.val,rvEssentialLabels_subset U.underlying.obj v.property⟩,hv,(hMap v).symm.trans hq⟩

end IntegrationInACVF.Section7
