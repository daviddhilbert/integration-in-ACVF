module

public import Integration7.BalancedUnaryVolumePreparation
public import Integration7.UnaryCompatiblePreparationWithoutField
public import Integration7.PreparedBalancedRVVolumeComparison
public import Integration7.GammaVolumeDensityRescaling
public import IntegrationSection6.GammaFiniteMixedBijections
public import Section5.GammaRestriction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The balanced unary preparations and their actual Gamma volume
comparison are constructed by Lemma5.2. Finite volume fibres are proved
from the original finite RV fibres; no prepared-comparison premise is added.
Every common nonzero constant density is allowed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {n a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 2400000 in
theorem balanced_unary_volume_preparation_without_field {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (hPS : P.real ⊆ S)
    (hcM : CanonicalStructure.IsCanonical (M := M))
    {R : Set (VF (M := M) × VF (M := M))} {ε : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (h : IsBalanced R ε r t) (hr : r ≠ rv (0 : VF (M := M)))
    (hrS : r.val ∈ S) (htS : t.val ∈ S) (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (η : RV (M := M)) (hηS : η.val ∈ S) (hη0 : η ≠ 0)
    (A B : DefSet (M := M) S 1 0) (f : Map A B) (hf : Function.Bijective f)
    (hAΓ : GammaSetDefinable P (carrier A)) (hBΓ : GammaSetDefinable P (carrier B))
    (hfΓ : GammaGraphDefinable P (pointMapGraph f))
    (hDomain : ∀ p : A, vfAt p.val 0 ∈ first R)
    (hValue : ∀ p : A, vfAt (f p).val 0 = ε (vfAt p.val 0)) :
    ∃ S' : Set M, ∃ hSS' : S ⊆ S', ∃ u v : ℕ,
      ∃ A' : DefSet (M := M) S' 1 u, ∃ B' : DefSet (M := M) S' 1 v,
      ∃ TA : SpecialBijection (extendBase A hSS') A', ∃ TB : SpecialBijection (extendBase B hSS') B',
      ∃ hTA : GammaChainDefinable P TA.chain, ∃ hTB : GammaChainDefinable P TB.chain,
      ∃ hA' : IsRVPullback (carrier A'), ∃ hB' : IsRVPullback (carrier B'),
      let hAF := gamma_special_pullback_finite_volume hκ.le hs hsmall TA hTA hA' (fun _ => Set.toFinite _)
      let hBF := gamma_special_pullback_finite_volume hκ.le hs hsmall TB hTB hB' (fun _ => Set.toFinite _)
      let U := rvFiniteEssential (canonicalFiniteRVObject hcM ⟨pullbackObject A',hAF⟩)
      let V := rvFiniteEssential (canonicalFiniteRVObject hcM ⟨pullbackObject B',hBF⟩)
      ∃ i : RVVolumeIso
        ((prependFixedRVVolume V r (hSS' hrS) (VolumeForm.one V.obj.domain)).rescale η (hSS' hηS) hη0)
        ((appendFixedRVVolume U t (hSS' htS) (VolumeForm.one U.obj.domain)).rescale η (hSS' hηS) hη0),
        i.GammaDefinable P := by
  obtain ⟨S',hSS',u,v,A',B',TA,TB,hTA,hTB,hA',hB',hc,hback,hgΓ,_⟩ :=
    lemma_5_2_gamma_presented_without_field hκ hs hsmall h00 γ hγ hγ1 hPS f hf hAΓ hBΓ hfΓ
  let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M N _ _ S S' A B f hSS'
  have hAF := gamma_special_pullback_finite_volume hκ.le hs hsmall TA hTA hA' (fun _ => Set.toFinite _)
  have hBF := gamma_special_pullback_finite_volume hκ.le hs hsmall TB hTB hB' (fun _ => Set.toFinite _)
  obtain ⟨i,hi⟩ := prepared_balanced_rv_volume_comparison hκ.le hs P hsmall (hPS.trans hSS') hcM h hr
    (hSS' hrS) (hSS' htS) hr0 ht0 fR hf (fun p => hDomain ⟨p.val,p.property⟩)
    (fun p => hValue ⟨p.val,p.property⟩) TA TB hA' hB'
    (GammaChainDefinable.target P TA.chain hTA) (GammaChainDefinable.target P TB.chain hTB)
    hc hback hgΓ hAF hBF
  exact ⟨S',hSS',u,v,A',B',TA,TB,hTA,hTB,hA',hB',i.rescale η (hSS' hηS) hη0,
    hi.rescale η (hSS' hηS) hη0⟩

end IntegrationInACVF.Section7
