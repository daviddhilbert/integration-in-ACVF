module

public import Integration7.GammaSliceLiftChartValues
public import Integration7.GammaVolumeSliceDensityAssembly
public import Integration7.LiteralRVVolumeForms
public import Integration7.MixedJacobianVFComparison
public import Integration7.FiniteVolumeParameterContexts
public import IntegrationSection6.GammaRVRealization

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A Gamma lift chart whose VF component follows a checked
Jacobian-one map has an actual volume-preserving realization in a small
containing context. Density is the retained old-label coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 1200000 in
theorem gamma_volume_lift_chart_realization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : GammaRVFiniteObject B 1) (hUC : U.codes ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (e : GammaIso B (carrier A) U.lift) (g : SpecialTransformations.Section5.Map A Z)
    (hJg : VFAlmostEverywhere (rawSpecialSet hc A) (fun p => HasMixedVFJacobianAt (rawSpecialMap hc g) p 1))
    (hVF : ∀ p : A, (e.equiv p).val.1 = (g p).val.1)
    (δ : Fin a) (ε : Fin (rvObjectArity U.object))
    (hε : ∀ u : rvObjectDomain U.object, (u.val ε).val ≠ iRVZero)
    (hLabel : ∀ p : A, (e.equiv p).val.2 ε = p.val.2 δ)
    (ω : VolumeForm (rawSpecialSet hc A)) (hDensity : ∀ p, ω.value p = p.val.2 δ) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ hUD : U.codes ⊆ (D.base : Set M),
      let UD := FiniteRV.gammaObjectAtExtend U hUD
      let Ω := gammaCoordinateDensityObject (e := 0) (k := 0) hc D U hUD ε hε
      ∃ f : SpecialTransformations.Section5.Map (extendBase A hCD) (typedLift UD.object.obj),
        Function.Bijective f ∧ GammaGraphDefinable B (pointMapGraph f) ∧
        (∀ p, (f p).val = (e.equiv ⟨p.val,p.property⟩).val) ∧
        PreservesVFVolume (ω.extend hCD)
          (literalRVVolumeForm hc UD.object Ω.form (typedLift UD.object.obj)
            (normalizedTypedLift_presents UD.object.obj)) (rawSpecialMap hc f) := by
  let e' := e.congr rfl (typedLift_carrier U.object).symm
  obtain ⟨d,t,hr⟩ := e'.graph.real_specialize
  let E := Set.range (rawTuple t)
  let D := finiteVolumeParameterContext C E (Set.finite_range _)
  have hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => finiteVolumeParameterContext_contains C E (Set.finite_range _) (Or.inl hx)
  have hQD : B.real ∪ Set.range (rawTuple t) ⊆ (D.base : Set M) := by
    rintro x (hx | hx)
    · exact hCD (hBC hx)
    · exact finiteVolumeParameterContext_contains C E (Set.finite_range _) (Or.inr hx)
  let hUD := hUC.trans hCD
  let UD := FiniteRV.gammaObjectAtExtend U hUD
  let Ω := gammaCoordinateDensityObject (e := 0) (k := 0) hc D U hUD ε hε
  let AD := extendBase A hCD
  let f : SpecialTransformations.Section5.Map AD (typedLift UD.object.obj) :=
    @Map.mk LRV M N _ _ (D.base : Set M) _ _ e'.equiv
      (@Space.RelationDefinable.mono LRV M N
        (@pointSpace M sM hM 1 a) (@pointSpace M sM hM 1 (rvObjectArity U.object))
        (B.real ∪ Set.range (rawTuple t)) (D.base : Set M) _ hr hQD)
  have hfValue (p : AD) : (f p).val = (e.equiv ⟨p.val,p.property⟩).val :=
    gammaIso_congr_value e rfl (typedLift_carrier U.object).symm p
  let gD := @Map.extend LRV M N _ _ (C.base : Set M) (D.base : Set M) A Z g hCD
  have hJD := hJg.extend hCD
  have hJf := vfJacobianOne_of_same_vf hc D Nat.one_pos (rawSpecialMap hc gD) (rawSpecialMap hc f) (by
    intro p
    change (g ⟨p.val,p.property⟩).val.1 = (f p).val.1
    rw [hfValue]
    exact (hVF ⟨p.val,p.property⟩).symm) hJD
  refine ⟨D,hCD,hUD,f,e'.equiv.bijective,e'.graph,hfValue,?_⟩
  apply hJf.mono
  intro p hJ
  refine ⟨1,hJ,?_⟩
  rw [RVOperations.rv_one,mul_one]
  rw [literalRVVolumeForm_density hc UD.object Ω.form (typedLift UD.object.obj)
    (normalizedTypedLift_presents UD.object.obj) ε (fun _ => rfl)]
  change ω.value ⟨p.val,p.property⟩ = (f p).val.2 ε
  rw [hDensity,hfValue]
  exact (hLabel ⟨p.val,p.property⟩).symm

end IntegrationInACVF.Section7
