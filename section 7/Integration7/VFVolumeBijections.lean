import Integration7.VFAlmostEverywhere
import IntegrationSection6.SmallVFFieldBases
import Section9.MixedDifferentiationAE

/-! Actual full definable volume-preserving bijections. These are
concrete witnesses used inside the later almost-everywhere category;
they do not identify a full bijection with a partially defined map. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b k : ℕ}

def PreservesVFVolume {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S}
    (ω : VolumeForm A) (π : VolumeForm B) (f : Map A B) : Prop :=
  VFAlmostEverywhere A (fun p => ∃ J : VFType (M := M),
    HasMixedVFJacobianAt f p J ∧ ω.value p = π.value (f p) * CanonicalRV.encodedRv J)

structure VFVolumeBijection (U V : PositiveVFVolumeObject (M := M) S k) where
  map : Map U.domain V.domain
  bijective : Function.Bijective map
  preserves : PreservesVFVolume U.form V.form map

/- The determinant argument is the local identity-chart argument of
Section9.SpecialJacobianGeneric, exposed here for arbitrary raw maps. -/
theorem mixedVFDerivative_det_one_of_preservesVF
    {A : Set ((Fin n → VFType (M := M)) × (Fin a → CanonicalRV.RVSort M))}
    {B : Set ((Fin n → VFType (M := M)) × (Fin b → CanonicalRV.RVSort M))}
    (f : A → B) (p : A)
    {L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M))}
    (hL : HasMixedVFDerivativeAt f p L) (h : ∀ p, (f p).val.1 = p.val.1) :
    (LinearMap.toMatrix' L).det = 1 := by
  obtain ⟨F, ⟨ρ, hρ⟩, hF⟩ := hL
  have he : Set.EqOn F id (vfBall p.val.1 ρ) := by
    intro x hx
    obtain ⟨hp, hFx⟩ := hρ x hx
    exact (congrArg Prod.fst hFx).symm.trans (h ⟨(x, p.val.2), hp⟩)
  have hId : HasVFDerivativeAt id p.val.1 LinearMap.id := by
    change HasVFDerivativeAt (fun x : Fin n → VFType (M := M) => x) p.val.1 LinearMap.id
    simpa only [LinearMap.id_apply, add_zero] using
      hasVFDerivativeAt_affine (LinearMap.id :
        (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M))) 0 p.val.1
  rw [(hF.congr_on_vfBall he).unique hId, LinearMap.toMatrix'_id, Matrix.det_one]

theorem vfJacobianOne_of_preservesVF
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (f : Map A B) (h : ∀ p, (f p).val.1 = p.val.1) :
    VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt f p 1) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
    Valued.mk' Values.presentationValuation
  obtain ⟨D, hDA, hd, hD⟩ := exists_mixedJacobianOne_exception hc C.saturated C.small hn f (by
    intro p hp
    obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc C.uncountable.le
      C.saturated C.small Values.presentation_compatible f p hp
    exact ⟨L, hL, mixedVFDerivative_det_one_of_preservesVF f p hL h⟩)
  exact ⟨D, hDA, hd, hD⟩

def VFVolumeBijection.of_preserving_vf_and_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : Map U.domain V.domain) (hf : Function.Bijective f)
    (hVF : ∀ p, (f p).val.1 = p.val.1)
    (hω : ∀ p, U.form.value p = V.form.value (f p)) : VFVolumeBijection U V where
  map := f
  bijective := hf
  preserves := (vfJacobianOne_of_preservesVF hc C (Nat.zero_lt_succ k) f hVF).mono
    (fun p hJ => ⟨1, hJ, by rw [RVOperations.rv_one, mul_one]; exact hω p⟩)

def VFVolumeBijection.refl
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) : VFVolumeBijection U U :=
  .of_preserving_vf_and_density hc C (Map.id U.domain) Function.bijective_id
    (fun _ => rfl) (fun _ => rfl)

def VFVolumeBijection.trans
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeBijection U V) (g : VFVolumeBijection V W) : VFVolumeBijection U W where
  map := g.map.comp f.map
  bijective := g.bijective.comp f.bijective
  preserves := by
    letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
    obtain ⟨D, hDA, hd, hD⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small
      (Nat.zero_lt_succ k) f.map g.map (Map.finiteFibres_of_injective f.bijective.1)
    have hchain : VFAlmostEverywhere U.domain (fun p => ∃ J K : VFType (M := M),
        HasMixedVFJacobianAt f.map p J ∧ HasMixedVFJacobianAt g.map (f.map p) K ∧
        HasMixedVFJacobianAt (g.map.comp f.map) p (K * J)) := ⟨D, hDA, hd, hD⟩
    have hboth := vfAlmostEverywhere_and hc C f.preserves
      (VFAlmostEverywhere.pullback_injective f.map f.bijective.1 g.preserves)
    apply (vfAlmostEverywhere_and hc C hboth hchain).mono
    rintro p ⟨⟨⟨J, hJ, hω⟩, ⟨K, hK, hπ⟩⟩, ⟨J', K', hJ', hK', hcomp⟩⟩
    have heJ := hJ'.unique hJ
    have heK := hK'.unique hK
    subst J'
    subst K'
    refine ⟨K * J, hcomp, ?_⟩
    change U.form.value p = W.form.value (g.map (f.map p)) * CanonicalRV.encodedRv (K * J)
    rw [RVOperations.rv_mul, hω, hπ, mul_assoc]

def VFVolumeBijection.symm
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeBijection U V) : VFVolumeBijection V U := by
  let g := f.map.inverse f.bijective
  have hfg (p : V.domain) : f.map (g p) = p := Map.apply_inverse _ _ p
  have hgf (p : U.domain) : g (f.map p) = p := Map.inverse_apply _ _ p
  have hginj : Function.Injective g := by
    intro p q he
    have h := congrArg f.map he
    simpa only [hfg] using h
  refine ⟨g, ⟨hginj, fun p => ⟨f.map p, hgf p⟩⟩, ?_⟩
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨D, hDA, hd, hD⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small
    (Nat.zero_lt_succ k) g f.map (Map.finiteFibres_of_injective hginj)
  have hchain : VFAlmostEverywhere V.domain (fun p => ∃ J K : VFType (M := M),
      HasMixedVFJacobianAt g p J ∧ HasMixedVFJacobianAt f.map (g p) K ∧
      HasMixedVFJacobianAt (f.map.comp g) p (K * J)) := ⟨D, hDA, hd, hD⟩
  have hid := vfJacobianOne_of_preservesVF hc C (Nat.zero_lt_succ k)
    (f.map.comp g) (fun p => congrArg (fun q : V.domain => q.val.1) (hfg p))
  have hforward := VFAlmostEverywhere.pullback_injective g hginj f.preserves
  apply (vfAlmostEverywhere_and hc C (vfAlmostEverywhere_and hc C hforward hchain) hid).mono
  rintro p ⟨⟨⟨K', hK', hω⟩, ⟨J, K, hJ, hK, hcomp⟩⟩, hId⟩
  have heK := hK.unique hK'
  subst K'
  have hprod : K * J = 1 := hcomp.unique hId
  refine ⟨J, hJ, ?_⟩
  change V.form.value p = U.form.value (g p) * CanonicalRV.encodedRv J
  rw [hω, hfg, mul_assoc, ← RVOperations.rv_mul, hprod, RVOperations.rv_one, mul_one]

end IntegrationInACVF.Section7
