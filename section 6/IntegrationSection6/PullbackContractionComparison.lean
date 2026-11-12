import IntegrationSection6.CanonicalFiniteContractionIsomorphisms
import IntegrationSection6.ArbitraryFiniteContractions

/-! Every finite standard contraction of an RV-pullback has the same Isp
class as its actual RV data. Canonical identity-head contractions supply
the comparison; arbitrary-order independence supplies all other choices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

theorem gamma_pullback_contraction_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs) (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S n a) (hU : GammaSetDefinable B (carrier U)) (hPull : IsRVPullback (carrier U))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program) :
    GammaIsp hκ.le hs h00 hreal (gammaPullbackAt hBS U hU hUF).toGamma
      (gammaFiniteContraction hκ.le hs hreal hBS hU hfin C hC) := by
  obtain ⟨D,hD,⟨e⟩⟩ := exists_canonical_finite_contraction_iso hκ.le hs hreal hBS U hU hPull hfin hUF
  exact (gamma_finite_contractions_all_orders hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 hBS
    U hU hfin D C hD hC).corollary_6_6 e (gammaIsoRefl _)

end IntegrationInACVF.Section6.FiniteRV
