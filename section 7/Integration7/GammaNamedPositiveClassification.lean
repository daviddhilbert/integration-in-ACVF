import Integration7.GammaNamedLiftSurjectivity
import Integration7.GammaNamedRVBlowupClasses

/-! Gamma-named positive-degree classes and the two directions of the volume
lift that do not need the Gamma prescribed-volume lifting theorem.

Over the Gamma-named base `B = ⟨C.base, Ξ⟩`, objects are actual volume
objects coded over `gammaNamedCodeContext C Ξ hΞ` (the real base together
with the common names of `B`) whose graphs are Gamma-definable over `B`.
VF classes are taken up to almost-everywhere VF volume isomorphisms with
Gamma graphs; RV classes up to Gamma common volume blowups.

* `gamma_named_lift_class_surjective`: every Gamma VF class is the class of
  the lift of a Gamma RV object (unconditional).
* `gamma_named_blowup_class_eq_of_lift_class_eq`: Gamma-isomorphic lifts have
  equal Gamma blowup classes (forward Proposition 7.8, unconditional; the
  Gamma intermediate densities come from `gamma_volume_transport_input`).

Well-definedness of the lift on Gamma blowup classes needs a Gamma version of
the prescribed-volume lifting theorem and is not claimed here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (GammaSetDefinable carrier)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {k : ℕ}

theorem rv_volume_lift_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U G) : VFVolumeObjectGamma (rvVolumeLift U) G := by
  have hL := gamma_rv_lift_carrier hc C hGC U hU
  have hD := gamma_rv_lift_carrier hc C hGC U.densityGraph (hU.densityGraph hc)
  have hDG : (volumeDensityGraph (rvVolumeLift U).form).carrier = (rvLift U.densityGraph.underlying.obj).carrier := by
    ext q
    constructor
    · rintro ⟨p,rfl⟩
      exact density_graph_lift_mem U p
    · intro hq
      obtain ⟨p,hp⟩ := (densityGraphLiftMap_bijective U).2 ⟨q,hq⟩
      exact ⟨p,congrArg Subtype.val hp⟩
  exact ⟨hL,hDG ▸ hD⟩

abbrev GammaVFVolumeObjects (G : Base (M := M)) (S : Set M) (k : ℕ) :=
  {U : PositiveVFVolumeObject (M := M) S k // VFVolumeObjectGamma U G}

def gammaVFVolumeIsoSetoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (k : ℕ) : Setoid (GammaVFVolumeObjects G (C.base : Set M) k) where
  r U V := ∃ f : VFVolumeIso U.val V.val, f.GammaDefinable G
  iseqv := ⟨fun U => ⟨VFVolumeIso.refl hc C U.val,U.property.refl_iso hc C⟩,
    fun ⟨f,hf⟩ => ⟨f.symm hc C,hf.symm hc C⟩,
    fun ⟨f,hf⟩ ⟨g,hg⟩ => ⟨f.trans hc C g,hf.trans hc C hg⟩⟩

/-- Positive-degree (`k+1` VF coordinates) VF volume classes over the Gamma base `G`,
coded over `C.base`, up to Gamma almost-everywhere volume isomorphisms. -/
abbrev GammaVFVolumeClasses (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (k : ℕ) := Quotient (gammaVFVolumeIsoSetoid hc C G k)

def gammaVFVolumeClass (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) {k : ℕ} (U : GammaVFVolumeObjects G (C.base : Set M) k) :
    GammaVFVolumeClasses hc C G k := Quotient.mk _ U

theorem gammaVFVolumeClass_eq_iff (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) {U V : GammaVFVolumeObjects G (C.base : Set M) k} :
    gammaVFVolumeClass hc C G U = gammaVFVolumeClass hc C G V ↔
      ∃ f : VFVolumeIso U.val V.val, f.GammaDefinable G :=
  ⟨fun h => Quotient.exact h,fun h => Quotient.sound (s := gammaVFVolumeIsoSetoid hc C G k) h⟩

/-- The lift of a Gamma RV volume object as a Gamma VF volume object. -/
def gammaVolumeLift (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (U : GammaVolumeObjects G (C.base : Set M) k) :
    GammaVFVolumeObjects G (C.base : Set M) k :=
  ⟨rvVolumeLift U.val,rv_volume_lift_gamma hc C hGC U.property⟩

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

/-- Every Gamma-named VF class is the class of a lift (unconditional). -/
theorem gamma_named_lift_class_surjective
    (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
    (A : GammaVFVolumeObjects (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M) k) :
    ∃ U : GammaVolumeObjects (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M) k,
      gammaVFVolumeClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) A =
        gammaVFVolumeClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
          (gammaVolumeLift hc (gammaNamedCodeContext C Ξ hΞ) (fun _ h => gamma_named_code_context_base C Ξ hΞ h) U) := by
  obtain ⟨P,e,he⟩ := GammaNamed.gamma_volume_lift_iso_exists hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
    (fun _ h => gamma_named_code_context_base C Ξ hΞ h) (gamma_named_code_context_names C Ξ hΞ) hGenerated A.val A.property
  exact ⟨P,(gammaVFVolumeClass_eq_iff hc _ _).mpr ⟨e,he⟩⟩

/-- Gamma-named forward Proposition 7.8 on classes. -/
theorem gamma_named_blowup_class_eq_of_lift_class_eq
    (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : GammaVolumeObjects (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M) k)
    (h : gammaVFVolumeClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
        (gammaVolumeLift hc (gammaNamedCodeContext C Ξ hΞ) (fun _ h => gamma_named_code_context_base C Ξ hΞ h) U) =
      gammaVFVolumeClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
        (gammaVolumeLift hc (gammaNamedCodeContext C Ξ hΞ) (fun _ h => gamma_named_code_context_base C Ξ hΞ h) V)) :
    gammaVolumeBlowupClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) U =
      gammaVolumeBlowupClass hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) V := by
  obtain ⟨f,hf⟩ := (gammaVFVolumeClass_eq_iff hc _ _).mp h
  exact (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
    (GammaNamed.gamma_volume_blowup_of_lift_iso hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ)
      (fun _ h => gamma_named_code_context_base C Ξ hΞ h) hΞ hGenerated
      (gamma_named_code_context_names C Ξ hΞ) (fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx)
      γ hγ hγ1 U V f hf)

end IntegrationInACVF.Section7
