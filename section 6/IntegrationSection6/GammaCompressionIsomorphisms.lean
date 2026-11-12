import IntegrationSection6.GammaFiniteCompression
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

def gammaPadIsoAt {U V : GammaObjectAt B S n} (e : GammaIsoAt U V) :
    GammaIsoAt (gammaPadAt U) (gammaPadAt V) :=
  GammaIsoAt.ofAmbient ((@rvPaddingFunctor M N hN S n).mapIso (isoAtAmbient e.iso)) e.graph

def gammaCompressIsoAt {U V : GammaObjectAt B S (n+1)}
    (hU : @rvLowWeightProperty M N S n U.object.obj) (hV : @rvLowWeightProperty M N S n V.object.obj)
    (e : GammaIsoAt U V) : GammaIsoAt (gammaCompressAt U hU) (gammaCompressAt V hV) :=
  GammaIsoAt.ofAmbient (@rvCompressIso M N S n U.object.obj V.object.obj hU hV (isoAtAmbient e.iso)) e.graph

def gammaLowRestrictionIsoAt {U V : GammaObjectAt B S (n+1)} (e : GammaIsoAt U V) :
    GammaIsoAt (gammaLowRestrictionAt U) (gammaLowRestrictionAt V) := by
  let E := @rvLowRestrictionIso M N S n U.object.obj V.object.obj (isoAtAmbient e.iso)
  apply GammaIsoAt.ofAmbient E
  exact gamma_rv_graph_restrict_source (isoAtMap e.iso) (@RVHom.map M N S (n+1) (@rvLowRestriction M N S n U.object.obj) (@rvLowRestriction M N S n V.object.obj) E.hom)
    (@rvLowDomain_subset M N S n U.object.obj) (gamma_low_volume_domain U.toGamma.toGammaRVObject) e.graph (fun _ => rfl)

def gammaWeightProjectionIsoAt {U V : GammaObjectAt B S (n+1)} (e : GammaIsoAt U V) :
    GammaIsoAt (gammaWeightProjectionAt U) (gammaWeightProjectionAt V) :=
  gammaCompressIsoAt _ _ (gammaLowRestrictionIsoAt e)

def gammaWeightProjectionPadIsoAt (U : GammaObjectAt B S n) :
    GammaIsoAt (gammaWeightProjectionAt (gammaPadAt U)) U := by
  let E := @rvWeightProjection_pad_iso M N hN S n U.object.obj
  apply GammaIsoAt.ofAmbient E
  apply GammaGraphDefinable.congr (gammaIsoRefl U.toGamma).graph
  intro p q
  constructor
  · rintro ⟨u,hu,hq⟩
    have hp : u.val ∈ carrier (rvObjectDomain (gammaWeightProjectionAt (gammaPadAt U)).object.obj) := by
      exact ⟨u,rfl,@rvPadding_label_has_zero M N hN n S (rvObjectVolume U.object.obj u)⟩
    exact ⟨⟨u.val,hp⟩,hu,hq⟩
  · rintro ⟨u,hu,hq⟩
    exact ⟨⟨u.val,@rvLowDomain_subset M N S n (@rvPadObject M N hN S n U.object.obj) u.val u.property⟩,hu,hq⟩

end IntegrationInACVF.Section6.FiniteRV
