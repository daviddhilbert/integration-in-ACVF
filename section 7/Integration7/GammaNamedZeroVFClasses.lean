import Integration7.GammaNamedZeroRVClasses
import Section9.GammaLiftObjects

/-! Gamma-named degree-zero VF volume objects (finite VF sets with nonzero
RV-valued densities), Gamma isomorphisms preserving densities, and the
Gamma degree-zero lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M}

/-- A degree-zero VF volume object with Gamma-definable set and density. -/
structure ZeroVFVolumeObject.Gamma (A : ZeroVFVolumeObject (M := M) S) (B : Base (M := M)) : Prop where
  set : GammaSetDefinable B (A.underlying.obj.obj.set.carrier :
    Set (Point (M := M) A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2))
  density : GammaGraphDefinable B (fun (p : Point (M := M) A.underlying.obj.obj.index.1
      A.underlying.obj.obj.index.2) (y : Point (M := M) 0 1) =>
    ∃ a : A.underlying.obj.obj.set, a.val = p ∧ (A.form.map a).val = y.2)

/-- A degree-zero VF volume isomorphism with a Gamma graph. -/
def ZeroVFVolumeIso.GammaDefinable {A A' : ZeroVFVolumeObject (M := M) S} (e : ZeroVFVolumeIso A A')
    (B : Base (M := M)) : Prop :=
  GammaGraphDefinable B (fun (p : Point (M := M) A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2)
    (q : Point (M := M) A'.underlying.obj.obj.index.1 A'.underlying.obj.obj.index.2) =>
      ∃ a : A.underlying.obj.obj.set, a.val = p ∧ (finiteZeroVFMap e.iso a).val = q)

theorem ZeroVFVolumeObject.Gamma.refl_iso {A : ZeroVFVolumeObject (M := M) S} (hA : A.Gamma B) :
    (ZeroVFVolumeIso.refl A).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph _ hA.set)
  intro p q
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl, rfl⟩
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a.property, rfl⟩

theorem ZeroVFVolumeIso.GammaDefinable.trans {A A' A'' : ZeroVFVolumeObject (M := M) S}
    {e : ZeroVFVolumeIso A A'} {f : ZeroVFVolumeIso A' A''} (he : e.GammaDefinable B)
    (hf : f.GammaDefinable B) : (e.trans f).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph he hf)
  intro p q
  constructor
  · rintro ⟨y, ⟨a, rfl, rfl⟩, b, hb, rfl⟩
    have : b = finiteZeroVFMap e.iso a := Subtype.ext hb
    subst this
    exact ⟨a, rfl, rfl⟩
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨_, ⟨a, rfl, rfl⟩, finiteZeroVFMap e.iso a, rfl, rfl⟩

theorem ZeroVFVolumeIso.GammaDefinable.symm {A A' : ZeroVFVolumeObject (M := M) S}
    {e : ZeroVFVolumeIso A A'} (he : e.GammaDefinable B) : (e.symm).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph he)
  intro p q
  constructor
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨finiteZeroVFMap e.iso a, rfl, congrArg Subtype.val (finiteZeroVFMap_symm_apply e.iso a)⟩
  · rintro ⟨b, rfl, rfl⟩
    exact ⟨finiteZeroVFMap e.iso.symm b, rfl, congrArg Subtype.val (finiteZeroVFMap_apply_symm e.iso b)⟩

abbrev GammaZeroVFObjects (B : Base (M := M)) (S : Set M) :=
  {A : ZeroVFVolumeObject (M := M) S // A.Gamma B}

def gammaZeroVFSetoid (B : Base (M := M)) (S : Set M) : Setoid (GammaZeroVFObjects B S) where
  r A A' := ∃ e : ZeroVFVolumeIso A.val A'.val, e.GammaDefinable B
  iseqv := ⟨fun A => ⟨ZeroVFVolumeIso.refl A.val, A.property.refl_iso⟩,
    fun ⟨e, he⟩ => ⟨e.symm, he.symm⟩, fun ⟨e, he⟩ ⟨f, hf⟩ => ⟨e.trans f, he.trans hf⟩⟩

/-- Gamma-named degree-zero VF volume classes. -/
abbrev GammaZeroVFClasses (B : Base (M := M)) (S : Set M) := Quotient (gammaZeroVFSetoid B S)

theorem zeroLift_gamma {U : ZeroRVVolumeObject (M := M) S} (hU : U.Gamma B) : (zeroLift U).Gamma B := by
  refine ⟨?_, ?_⟩
  · have he : ((zeroLift U).underlying.obj.obj.set.carrier : Set (Point (M := M) 0 U.underlying.obj.arity)) =
        {p | p.2 ∈ U.underlying.obj.domain.carrier} := by
      ext p
      constructor
      · rintro ⟨u, hu, _⟩
        change p.2 ∈ U.underlying.obj.domain.carrier
        rw [← hu]
        exact u.property
      · intro hp
        exact ⟨⟨p.2, hp⟩, rfl, funext (fun i => Fin.elim0 i)⟩
    exact he ▸ hU.domain
  · apply SpecialTransformations.Section5.GammaGraphDefinable.congr hU.density
    intro p y
    constructor
    · rintro ⟨u, hu, hy⟩
      refine ⟨⟨p, u, hu, funext (fun i => Fin.elim0 i)⟩, rfl, ?_⟩
      rw [← hy]
      change (U.form.map (liftLabelMap U.underlying.obj ⟨p, u, hu, funext (fun i => Fin.elim0 i)⟩)).val = (U.form.map u).val
      congr 2
      exact Subtype.ext hu.symm
    · rintro ⟨a, rfl, hy⟩
      exact ⟨liftLabelMap U.underlying.obj a, rfl, hy⟩

theorem zeroLiftIso_gamma {U V : ZeroRVVolumeObject (M := M) S} (e : ZeroRVVolumeIso U V)
    (he : e.GammaDefinable B) : (zeroLiftIso e).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr he
  intro p q
  constructor
  · rintro ⟨u, hu, hq⟩
    refine ⟨⟨p, u, hu, funext (fun i => Fin.elim0 i)⟩, rfl, ?_⟩
    have hl : liftLabelMap U.underlying.obj ⟨p, u, hu, funext (fun i => Fin.elim0 i)⟩ = u :=
      Subtype.ext hu.symm
    refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
    change ((liftLabelMap V.underlying.obj).inverse (zero_lift_label_map_bijective V.underlying.obj)
      (finiteIsoMap e.iso (liftLabelMap U.underlying.obj ⟨p, u, hu, funext (fun i => Fin.elim0 i)⟩))).val.2 = q.2
    rw [hl, ← hq]
    exact congrArg Subtype.val (Map.apply_inverse (liftLabelMap V.underlying.obj)
      (zero_lift_label_map_bijective V.underlying.obj) (finiteIsoMap e.iso u))
  · rintro ⟨a, rfl, rfl⟩
    refine ⟨liftLabelMap U.underlying.obj a, rfl, ?_⟩
    change _ = ((liftLabelMap V.underlying.obj).inverse (zero_lift_label_map_bijective V.underlying.obj)
      (finiteIsoMap e.iso (liftLabelMap U.underlying.obj a))).val.2
    exact (congrArg Subtype.val (Map.apply_inverse (liftLabelMap V.underlying.obj)
      (zero_lift_label_map_bijective V.underlying.obj) _)).symm

theorem zeroRVOfLiftIso_gamma {U V : ZeroRVVolumeObject (M := M) S}
    (e : ZeroVFVolumeIso (zeroLift U) (zeroLift V)) (he : e.GammaDefinable B) :
    (zeroRVOfLiftIso e).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr he
  intro p q
  constructor
  · rintro ⟨a, rfl, rfl⟩
    refine ⟨liftLabelMap U.underlying.obj a, rfl, ?_⟩
    change (liftLabelMap V.underlying.obj (finiteZeroVFMap e.iso
      ((liftLabelMap U.underlying.obj).inverse (zero_lift_label_map_bijective U.underlying.obj)
        (liftLabelMap U.underlying.obj a)))).val = _
    rw [Map.inverse_apply]
    rfl
  · rintro ⟨u, hu, hq⟩
    let a := (liftLabelMap U.underlying.obj).inverse (zero_lift_label_map_bijective U.underlying.obj) u
    have ha : liftLabelMap U.underlying.obj a = u := Map.apply_inverse _ _ u
    refine ⟨a, Prod.ext (funext (fun i => Fin.elim0 i)) ?_, ?_⟩
    · rw [← hu]
      exact congrArg Subtype.val ha
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      rw [← hq]
      rfl

end IntegrationInACVF.Section7.HK
