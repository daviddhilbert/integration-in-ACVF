import Integration7.HKZeroVolumeIntegration
import Integration7.GammaNamedLiftClasses

/-! Gamma-named degree-zero RV volume objects (HK's weighted convention:
finite RV objects with nonzero RV-valued densities), Gamma isomorphisms
preserving the density exactly, and their classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M}

/-- A degree-zero RV volume object with Gamma-definable domain and density. -/
structure ZeroRVVolumeObject.Gamma (U : ZeroRVVolumeObject (M := M) S) (B : Base (M := M)) : Prop where
  domain : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ U.underlying.obj.domain.carrier}
  density : RVMapGamma U.form.map B

/-- A degree-zero RV volume isomorphism with a Gamma graph. -/
def ZeroRVVolumeIso.GammaDefinable {U V : ZeroRVVolumeObject (M := M) S} (e : ZeroRVVolumeIso U V)
    (B : Base (M := M)) : Prop :=
  RVMapGamma (finiteIsoMap e.iso) B

theorem ZeroRVVolumeObject.Gamma.refl_iso {U : ZeroRVVolumeObject (M := M) S} (hU : U.Gamma B) :
    (ZeroRVVolumeIso.refl U).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph _ hU.domain)
  intro p q
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨p.2, hp⟩, rfl, rfl⟩
  · rintro ⟨u, hu, hv⟩
    refine ⟨?_, ?_⟩
    · change p.2 ∈ U.underlying.obj.domain.carrier
      rw [← hu]
      exact u.property
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      rw [← hu]
      exact hv

theorem ZeroRVVolumeIso.GammaDefinable.trans {U V W : ZeroRVVolumeObject (M := M) S}
    {e : ZeroRVVolumeIso U V} {f : ZeroRVVolumeIso V W} (he : e.GammaDefinable B) (hf : f.GammaDefinable B) :
    (e.trans f).GammaDefinable B := by
  have h := RVMapGamma.comp he hf
  apply RVMapGamma.congr h
  intro u
  rfl

theorem ZeroRVVolumeIso.GammaDefinable.symm {U V : ZeroRVVolumeObject (M := M) S}
    {e : ZeroRVVolumeIso U V} (he : e.GammaDefinable B) : (e.symm).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph he)
  intro p q
  constructor
  · rintro ⟨u, hu, hv⟩
    refine ⟨finiteIsoMap e.iso u, hv, ?_⟩
    rw [← hu]
    exact congrArg Subtype.val
      (SpecialTransformations.Section7.rvIso_inv_apply ((finiteVolumeProperty S 0).ι.mapIso e.iso) u)
  · rintro ⟨v, hv, hu⟩
    refine ⟨finiteIsoMap e.iso.symm v, hu, ?_⟩
    rw [← hv]
    exact congrArg Subtype.val
      (SpecialTransformations.Section7.rvIso_inv_apply ((finiteVolumeProperty S 0).ι.mapIso e.iso).symm v)

abbrev GammaZeroRVObjects (B : Base (M := M)) (S : Set M) :=
  {U : ZeroRVVolumeObject (M := M) S // U.Gamma B}

def gammaZeroRVSetoid (B : Base (M := M)) (S : Set M) : Setoid (GammaZeroRVObjects B S) where
  r U V := ∃ e : ZeroRVVolumeIso U.val V.val, e.GammaDefinable B
  iseqv := ⟨fun U => ⟨ZeroRVVolumeIso.refl U.val, U.property.refl_iso⟩,
    fun ⟨e, he⟩ => ⟨e.symm, he.symm⟩, fun ⟨e, he⟩ ⟨f, hf⟩ => ⟨e.trans f, he.trans hf⟩⟩

/-- Gamma-named degree-zero RV volume classes. -/
abbrev GammaZeroRVClasses (B : Base (M := M)) (S : Set M) := Quotient (gammaZeroRVSetoid B S)

end IntegrationInACVF.Section7.HK
