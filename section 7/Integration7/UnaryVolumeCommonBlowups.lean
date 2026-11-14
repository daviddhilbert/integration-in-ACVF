import Integration7.UnarySmallContextPreparation
import Integration7.UnaryVolumeChainCorollary
import Integration7.UnaryPullbackVolumeComparison
import Integration7.SpecialVolumeConjugacy
import Integration7.LiteralRVVolumeForms
import Integration7.PositiveVolumeParameterExtension

/-! The unary volume analogue of Corollary6.11. Compatible preparations
are constructed in a genuine small containing context; their actual chains
give common forward volume blowups, and lift descent proves the final iso. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (carrier extendBase GammaSetDefinable GammaGraphDefinable pointMapGraph)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem corollary_6_11_unary_volume_presented
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaParameters.Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (FBase : VFFieldBase P.real)
    (F G : @RVFiniteObject M N (C.base : Set M) 1)
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    (π : VolumeForm (canonicalFiniteRVObject hc G).obj.domain)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1
      (@RVObject.arity M N (C.base : Set M) 1 F.obj))
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1
      (@RVObject.arity M N (C.base : Set M) 1 G.obj))
    (hA : @Section6.PresentsLift M N hN (C.base : Set M) 1 F.obj (Section6.normalizedPointSet A))
    (hB : @Section6.PresentsLift M N hN (C.base : Set M) 1 G.obj (Section6.normalizedPointSet B))
    (δ : Fin (@RVObject.arity M N (C.base : Set M) 1 F.obj))
    (ε : Fin (@RVObject.arity M N (C.base : Set M) 1 G.obj))
    (hω : ∀ u, ω.value u = u.val δ) (hπ : ∀ u, π.value u = u.val ε)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hAΓ : GammaSetDefinable P (carrier A)) (hBΓ : GammaSetDefinable P (carrier B))
    (hfΓ : GammaGraphDefinable P (pointMapGraph f))
    (hMeasure : PreservesVFVolume (literalRVVolumeForm hc F ω A hA)
      (literalRVVolumeForm hc G π B hB) (rawSpecialMap hc f)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      VolumeBlowupEquivalent
        ((⟨canonicalFiniteRVObject hc F, ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) 0).extend hCD)
        ((⟨canonicalFiniteRVObject hc G, π⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) 0).extend hCD) := by
  obtain ⟨D, hCD, r, s, A', B', TA, TB, hTA, hTB, hA', hB', hcon, hback, hgΓ, _⟩ :=
    unary_bijection_preparation_in_context C P hPC γ hγ hγ1 FBase f hf hAΓ hBΓ hfΓ
  let FD := @Section6.FiniteRV.extendObject M N (C.base : Set M) (D.base : Set M) 1 hCD F
  let GD := @Section6.FiniteRV.extendObject M N (C.base : Set M) (D.base : Set M) 1 hCD G
  let AD := extendBase A hCD
  let BD := extendBase B hCD
  let fD : SpecialTransformations.Section5.Map AD BD :=
    @SpecialTransformations.DefinableGeometry.Map.extend LRV M N
      (SpecialTransformations.Section5.pointSpace 1 (@RVObject.arity M N (C.base : Set M) 1 F.obj))
      (SpecialTransformations.Section5.pointSpace 1 (@RVObject.arity M N (C.base : Set M) 1 G.obj))
      (C.base : Set M) (D.base : Set M) A B f hCD
  have hAD := Section6.normalizedPresentsLift_extendBase hCD hA
  have hBD := Section6.normalizedPresentsLift_extendBase hCD hB
  have hωD : ∀ u, (ω.extend hCD).value u = u.val δ :=
    fun u => hω ⟨u.val, u.property⟩
  have hπD : ∀ u, (π.extend hCD).value u = u.val ε :=
    fun u => hπ ⟨u.val, u.property⟩
  obtain ⟨hAF, hδA, WA, hWA, ⟨eA⟩⟩ :=
    corollary_6_10_unary_volume hc D FD (ω.extend hCD) hAD δ hωD TA
  obtain ⟨hBF, hεB, WB, hWB, ⟨eB⟩⟩ :=
    corollary_6_10_unary_volume hc D GD (π.extend hCD) hBD ε hπD TB
  let ωD := literalRVVolumeForm hc FD (ω.extend hCD) AD hAD
  let πD := literalRVVolumeForm hc GD (π.extend hCD) BD hBD
  let θA := rawPullbackVolumeForm hc A' hA' hAF (TA.chain.labelIndex δ) hδA
  let θB := rawPullbackVolumeForm hc B' hB' hBF (TB.chain.labelIndex ε) hεB
  have hmD : PreservesVFVolume ωD πD (rawSpecialMap hc fD) :=
    hMeasure.extend hCD
  have hωT : ∀ p, ωD.value p = θA.value ((rawSpecialMap hc TA.toMap) p) :=
    special_retained_volume_density hc TA hA' hAF δ hδA ωD
      (literalRVVolumeForm_density hc FD (ω.extend hCD) AD hAD δ hωD)
  have hπT : ∀ p, πD.value p = θB.value ((rawSpecialMap hc TB.toMap) p) :=
    special_retained_volume_density hc TB hB' hBF ε hεB πD
      (literalRVVolumeForm_density hc GD (π.extend hCD) BD hBD ε hπD)
  have hm := unary_volume_conjugate hc D TA TB fD hf ωD πD θA θB hωT hπT hmD
  let g := IntegrationInACVF.Section5.unaryConjugate TA TB fD
  have hg := IntegrationInACVF.Section5.unaryConjugate_bijective TA TB fD hf
  let e := unaryPullbackVolumeIso hc D P (hPC.trans hCD) A' B' hA' hB' hAF hBF
    (TA.chain.labelIndex δ) (TB.chain.labelIndex ε) hδA hεB g hg hcon hback hgΓ hm
  refine ⟨D, hCD, TA.length, TB.length, WA, WB, ?_, ?_, ?_⟩
  · exact hWA
  · exact hWB
  · exact ⟨(eA.trans hc D e).trans hc D (eB.symm hc D)⟩

end IntegrationInACVF.Section7
