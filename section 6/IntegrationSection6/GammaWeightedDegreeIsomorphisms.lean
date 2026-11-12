import IntegrationSection6.GammaNonzeroResolutions
import IntegrationSection6.GammaCompressionIsomorphisms
import IntegrationSection6.FiniteGammaAmbientIsos
import Section4.RVPaddingSplit
import IntegrationSection6.GammaWeightStrata
import Section4.RVFinitePadding
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

structure GammaWeightedIsoAt {i j : ℕ} (U : GammaObjectAt B S i) (V : GammaObjectAt B S j) where
  map : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj)
  bijective : Function.Bijective map
  graph : GammaGraphDefinable B (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj))
    (q : Point (M := M) 0 (rvObjectArity V.object.obj)) =>
      ∃ u : rvObjectDomain U.object.obj, u.val = p.2 ∧ (map u).val = q.2)
  weight : ∀ u : rvObjectDomain U.object.obj,
    @rvWeight M N i (@RVObject.value M N S i U.object.obj u) =
      @rvWeight M N j (@RVObject.value M N S j V.object.obj (map u))

def GammaWeightedIsoAt.toIso {i : ℕ} {U V : GammaObjectAt B S i} (e : GammaWeightedIsoAt U V) : GammaIsoAt U V := {
  iso := @isoOfDefinableBijection M N S i U.object V.object e.map e.bijective e.weight
  graph := e.graph }

def GammaWeightedIsoAt.compressTarget {i j : ℕ} {U : GammaObjectAt B S i} {V : GammaObjectAt B S (j+1)}
    (e : GammaWeightedIsoAt U V) (hV : @rvLowWeightProperty M N S j V.object.obj) :
    GammaWeightedIsoAt U (gammaCompressAt V hV) where
  map := e.map
  bijective := e.bijective
  graph := e.graph
  weight u := (e.weight u).trans (@rvCompressObject_weight M N S j V.object.obj hV (e.map u)).symm

def GammaWeightedIsoAt.compressSource {i j : ℕ} {U : GammaObjectAt B S (i+1)} {V : GammaObjectAt B S j}
    (e : GammaWeightedIsoAt U V) (hU : @rvLowWeightProperty M N S i U.object.obj) :
    GammaWeightedIsoAt (gammaCompressAt U hU) V where
  map := e.map
  bijective := e.bijective
  graph := e.graph
  weight u := (@rvCompressObject_weight M N S i U.object.obj hU u).trans (e.weight u)

theorem GammaWeightedIsoAt.target_low {i j : ℕ} {U : GammaObjectAt B S i} {V : GammaObjectAt B S (j+1)}
    (e : GammaWeightedIsoAt U V) (hij : i ≤ j) : @rvLowWeightProperty M N S j V.object.obj := by
  intro v
  obtain ⟨u,rfl⟩ := e.bijective.2 v
  exact (e.weight u).symm.le.trans ((@rvWeight_le_arity M N i (@RVObject.value M N S i U.object.obj u)).trans hij)

theorem GammaWeightedIsoAt.source_low {i j : ℕ} {U : GammaObjectAt B S (i+1)} {V : GammaObjectAt B S j}
    (e : GammaWeightedIsoAt U V) (hji : j ≤ i) : @rvLowWeightProperty M N S i U.object.obj := by
  intro u
  exact (e.weight u).le.trans ((@rvWeight_le_arity M N j (@RVObject.value M N S j V.object.obj (e.map u))).trans hji)

end IntegrationInACVF.Section6.FiniteRV
