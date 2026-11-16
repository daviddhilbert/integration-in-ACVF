module

public import Integration7.HKZeroRVVolumeIsomorphisms
public import Section10.WeightedZeroResults

@[expose] public section

/-! Exact adapters from the sequel's retained proof presentations to the
published weighted-zero category. Both directions retain the definable map
of the form. Thus the staged proofs use precisely the upstream objects and
the upstream notion of isomorphism, including actual RV weights. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section10

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {P : Space LRV M} {A : DefSet P S}

def formToUpstream (ω : VolumeForm A) : ZeroForm rvVolumeScale A :=
  ⟨ω.map, ω.nonzero⟩

def formFromUpstream (ω : ZeroForm rvVolumeScale A) : VolumeForm A :=
  ⟨ω.map, ω.allowed⟩

def upstreamFormEquiv : VolumeForm A ≃ ZeroForm rvVolumeScale A where
  toFun := formToUpstream
  invFun := formFromUpstream
  left_inv ω := by cases ω; rfl
  right_inv ω := by cases ω; rfl

@[simp] theorem formToUpstream_weight (ω : VolumeForm A) (a : A) :
    (formToUpstream ω).weight a = ω.value a := rfl

def ZeroRVVolumeObject.toUpstream (U : ZeroRVVolumeObject (M := M) S) :
    MeasuredRVZero S rvVolumeScale := ⟨U.underlying, formToUpstream U.form⟩

def ZeroRVVolumeObject.fromUpstream (U : MeasuredRVZero (M := M) S rvVolumeScale) :
    ZeroRVVolumeObject S := ⟨U.underlying, formFromUpstream U.form⟩

def upstreamRVZeroEquiv (S : Set M) :
    ZeroRVVolumeObject (M := M) S ≃ MeasuredRVZero S rvVolumeScale where
  toFun := ZeroRVVolumeObject.toUpstream
  invFun := ZeroRVVolumeObject.fromUpstream
  left_inv U := by cases U with | mk U ω => cases ω; rfl
  right_inv U := by cases U with | mk U ω => cases ω; rfl

@[simp] theorem ZeroRVVolumeObject.toUpstream_weight (U : ZeroRVVolumeObject (M := M) S)
    (u : U.underlying.obj.domain) : U.toUpstream.weight u = U.form.value u := rfl

def ZeroRVVolumeIso.toUpstream {U V : ZeroRVVolumeObject (M := M) S}
    (e : ZeroRVVolumeIso U V) : U.toUpstream ≅ V.toUpstream :=
  WeightedZero.isoOfExactMap ⟨finiteIsoMap e.iso, finiteIsoMap_bijective e.iso, e.density⟩

def ZeroRVVolumeIso.fromUpstream {U V : ZeroRVVolumeObject (M := M) S}
    (e : U.toUpstream ≅ V.toUpstream) : ZeroRVVolumeIso U V :=
  ZeroRVVolumeIso.ofBijection e.hom.map e.hom.bijective e.hom.preserves

theorem upstream_zero_iso_iff (U V : ZeroRVVolumeObject (M := M) S) :
    Nonempty (U.toUpstream ≅ V.toUpstream) ↔ Nonempty (ZeroRVVolumeIso U V) :=
  ⟨fun ⟨e⟩ => ⟨ZeroRVVolumeIso.fromUpstream e⟩,
    fun ⟨e⟩ => ⟨e.toUpstream⟩⟩

end IntegrationInACVF.Section7.HK
