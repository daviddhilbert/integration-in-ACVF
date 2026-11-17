module

public import Integration7.UnaryVolumeContractionConjugacy
public import Integration7.GammaUnaryVolumeCommonSchemaWithoutField
public import Integration7.ContractionRetainedDensityLabels
public import IntegrationSection6.FiniteStandardContractions
public import Integration7.GammaVolumeSliceDensityAssembly

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual arbitrary unary contractions of measure-preservingly
isomorphic mixed sets have common volume-blowup formula witnesses.
The input volume equation is almost everywhere, as in the VF category. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B₀ : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 3200000 in
theorem unary_contraction_common_volume_schema {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B₀.real < κ) (hgamma : Cardinal.mk B₀.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBC : B₀.real ∪ Set.range z ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B₀.gamma) (hγ1 : 1 < γ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b)
    (hA : GammaSetDefinable ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ (carrier A))
    (hB : GammaSetDefinable ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ (carrier B))
    (hfinA : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin 1 → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hfΓ : GammaGraphDefinable ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ (pointMapGraph f))
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (E : StandardContraction B τ)
    (hT : GammaProgramDefinable ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ T.program)
    (hE : GammaProgramDefinable ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ E.program)
    (L : GammaRVVolumeSchema B₀ p (1+T.arity) 0 sp)
    (R : GammaRVVolumeSchema B₀ p (1+E.arity) 0 sp)
    (hL : L.valid z) (hR : R.valid z) :
    let Bz : Base (M := M) := ⟨B₀.real ∪ Set.range z,B₀.gamma⟩
    let U := FiniteRV.gammaFiniteContraction hκ hs (small_union_range hκ B₀.real hreal z) hBC hA hfinA T hT
    let V := FiniteRV.gammaFiniteContraction hκ hs (small_union_range hκ B₀.real hreal z) hBC hB hfinB E hE
    ∀ (hδ : ∀ u : rvObjectDomain U.object, (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero)
      (hε : ∀ v : rvObjectDomain V.object, (v.val (FiniteRV.contractionOldLabelIndex E ε)).val ≠ iRVZero),
    RVVolumeSchemaRow (gammaCoordinateDensityObject (e := 0) (k := 0) hc C U (Set.Subset.refl _) _ hδ) L z →
    RVVolumeSchemaRow (gammaCoordinateDensityObject (e := 0) (k := 0) hc C V (Set.Subset.refl _) _ hε) R z →
    ∃ H : GammaVolumeCommonSchema L R, H.valid z := by
  intro Bz U V hδ hε PL PR
  let UD := FiniteRV.gammaObjectAtExtend U (Set.Subset.refl _)
  let VD := FiniteRV.gammaObjectAtExtend V (Set.Subset.refl _)
  let Ω := gammaCoordinateDensityObject (e := 0) (k := 0) hc C U (Set.Subset.refl _) _ hδ
  let Θ := gammaCoordinateDensityObject (e := 0) (k := 0) hc C V (Set.Subset.refl _) _ hε
  let t := typedContractionNaturalMap T
  let e := typedContractionNaturalMap E
  have htΓ : GammaGraphDefinable Bz (pointMapGraph t) :=
    T.gamma_normalized_natural_graph hBC hA hT
  have heΓ : GammaGraphDefinable Bz (pointMapGraph e) :=
    E.gamma_normalized_natural_graph hBC hB hE
  let g := unaryContractionConjugate f T E
  have hg := unaryContractionConjugate_bijective f hf T E
  have hgΓ : GammaGraphDefinable Bz (pointMapGraph g) :=
    gamma_composition_graph _ e
      (gamma_composition_graph _ f (gamma_inverse_map_graph t (typedContractionNaturalMap_bijective T) htΓ) hfΓ) heΓ
  have hUA : GammaSetDefinable Bz (carrier (typedLift U.object)) := by
    rw [typedLift_carrier]
    exact U.toGammaRVObject.lift_definable
  have hVA : GammaSetDefinable Bz (carrier (typedLift V.object)) := by
    rw [typedLift_carrier]
    exact V.toGammaRVObject.lift_definable
  have hMeasure := unary_contraction_conjugate_preserves_volume hc C f hf ω π hm T E
  have hMeasure' : PreservesVFVolume
      (literalRVVolumeForm hc UD.object Ω.form (typedLift U.object) (normalizedTypedLift_presents U.object))
      (literalRVVolumeForm hc VD.object Θ.form (typedLift V.object) (normalizedTypedLift_presents V.object))
      (rawSpecialMap hc g) := by
    apply hMeasure.mono
    rintro q ⟨J,hJ,hJω⟩
    refine ⟨J,hJ,?_⟩
    rw [unaryContractionLiftForm_density hc T ω δ hω,
      unaryContractionLiftForm_density hc E π ε hπ] at hJω
    rw [literalRVVolumeForm_density hc UD.object Ω.form _ _ _ (fun _ => rfl),
      literalRVVolumeForm_density hc VD.object Θ.form _ _ _ (fun _ => rfl)]
    exact hJω
  exact gamma_unary_volume_common_schema_without_field hc C hκ hs hreal hgamma z hz hBC γ hγ hγ1
    UD.object VD.object Ω.form Θ.form (typedLift U.object) (typedLift V.object)
    (normalizedTypedLift_presents U.object) (normalizedTypedLift_presents V.object)
    (FiniteRV.contractionOldLabelIndex T δ) (FiniteRV.contractionOldLabelIndex E ε)
    (fun _ => rfl) (fun _ => rfl) g hg hUA hVA hgΓ hMeasure' L R hL hR PL PR

end IntegrationInACVF.Section7
