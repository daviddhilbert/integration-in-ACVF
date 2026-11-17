module

public import Integration7.PullbackVolumeMapDescent
public import IntegrationSection5.UnaryRVCategory

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The unary RV comparison for a mutually contractible actual volume
bijection. Section5.3 constructs the compatible RV isomorphism; the checked
lift descent supplies both volume equations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (pullbackObject rvObjectVolume IsRVPullback carrier
  Contractible pointMapGraph GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

def unaryPullbackVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaParameters.Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    {a b : ℕ}
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (hBF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject B)))
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hcon : Contractible f)
    (hback : Contractible (SpecialTransformations.Section5.Map.inverse f hf))
    (hfΓ : GammaGraphDefinable P (pointMapGraph f))
    (hMeasure : PreservesVFVolume (rawPullbackVolumeForm hc A hA hAF δ hδ)
      (rawPullbackVolumeForm hc B hB hBF ε hε) (rawSpecialMap hc f)) :
    RVVolumeIso (pullbackCoordinateVolumeObject hc A hAF δ hδ)
      (pullbackCoordinateVolumeObject hc B hBF ε hε) := by
  have hsmall : Cardinal.mk P.real < C.κ :=
    (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
  let e := IntegrationInACVF.Section5.unaryRVIso C.uncountable.le C.saturated hsmall
    f hf hcon hback hA hB hfΓ
  exact pullbackVolumeIsoOfCompatibleMap hc C A B hA hB hAF hBF δ ε hδ hε f hf e
    (IntegrationInACVF.Section5.unaryRVIso_spec C.uncountable.le C.saturated hsmall
      f hf hcon hback hA hB hfΓ) hMeasure

end IntegrationInACVF.Section7
