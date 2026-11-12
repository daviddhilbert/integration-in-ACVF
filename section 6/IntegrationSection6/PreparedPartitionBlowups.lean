import IntegrationSection6.PreparedMixedPartitions
import IntegrationSection6.FiniteGammaChartedChains
import IntegrationSection6.GammaIspUniversalPresentation

/-! Simultaneous special preparation of a lift partition gives an actual
finite RV object Isp-equivalent to the original one, over its unchanged base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ} {ι : Type} [Fintype ι]
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem prepared_partition_blowup {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ n)
    (D : ι → DefSet (M := M) Set.univ n (rvObjectArity U.object.obj))
    (P : PreparedMixedPartition (B := B) (typedLift U.object.obj) D) :
    ∃ hPF : Map.FiniteFibres (rvObjectVolume (pullbackObject P.target)),
      GammaIsp hκ hs h00 hreal U.toGamma
        (gammaPullbackAt (Set.subset_univ _) P.target (GammaChainDefinable.target B P.special.chain P.gamma) hPF).toGamma := by
  obtain ⟨hPF,H⟩ := (gammaChain_charted_pair hκ hs h00 hreal (Set.subset_univ _) P.special.chain P.gamma).1
    (@RVObject.domain M N Set.univ n U.object.obj) (@RVObject.volume M N Set.univ n U.object.obj)
    U.object.property (normalizedTypedLift_presents U.object.obj) P.special.alternating
  let V := gammaPullbackAt (Set.subset_univ _) P.target (GammaChainDefinable.target B P.special.chain P.gamma) hPF
  have HAt : GammaIspAt hκ hs h00 hreal U V :=
    ⟨P.special.length,0,V,V,H,GammaIteratedBlowup.refl V,⟨GammaIsoAt.refl V⟩⟩
  exact ⟨hPF,HAt.to_global⟩

end IntegrationInACVF.Section6.FiniteRV
