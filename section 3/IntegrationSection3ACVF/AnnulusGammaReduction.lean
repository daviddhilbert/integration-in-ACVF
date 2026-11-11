import IntegrationSection3ACVF.DefinableGammaMatching
import IntegrationSection3ACVF.RadialAnnulusDomains
import IntegrationSection3ACVF.RadialValuePullbacks

/-! The corrected3.24 geometry reduces to an actual definable bijection
from a closed Gamma interval to either a half-open interval or a closed ray.
The targetVFcase is preserved, and both hole-centre labels are explicit. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AnnulusGammaReduction

open PuncturedGeometry GammaRadiusAtomicity RadialOpenClasses

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem radial_to_gamma {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (a b : VFType (M := M)) (V W : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) (hW : Values.infinity ∉ W) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (domain a V) f))
    (hbij : Set.BijOn f (domain a V) (domain b W))
    (hoo : MaximalOpenClasses.OpenToOpen (domain a V) f) :
    ∃ e : {γ : Values.Gamma (M := M) | γ.val ∈ V} → {η : Values.Gamma (M := M) | η.val ∈ W},
      Function.Bijective e ∧ FullGammaSyntax.Definable (RealParameterTuples.extend B ![a.val,b.val])
        (DefinableGammaMatching.graph {γ | γ.val ∈ V} {η | η.val ∈ W} e) := by
  obtain ⟨g,hg,hGraph,_⟩ := RadialQuotientGraph.exists_definable_rv_bijection B a b V W hV hW f hf hbij hoo
  have hA := RadialValuePullbacks.image_eq_pullback a V hV
  have hB := RadialValuePullbacks.image_eq_pullback b W hW
  change Set.BijOn g (RadialRVImages.image a V) (RadialRVImages.image b W) at hg
  change FullBaseAtomicity.OverBase (RealParameterTuples.extend B ![a.val,b.val])
    (ImaginaryBaseImages.graphOn (RadialRVImages.image a V) g) at hGraph
  rw [hA,hB] at hg
  rw [hA] at hGraph
  exact DefinableGammaMatching.exists_definable_gamma_bijection hκ hs h00
    (RealParameterTuples.extend B ![a.val,b.val]) (RealParameterTuples.small hκ B hsmall ![a.val,b.val])
    {γ | γ.val ∈ V} {η | η.val ∈ W} g hGraph hg

theorem closed_to_open {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (d e : PuncturedBall M) (a c k : VFType (M := M)) (ρ τ ν : Values.Gamma (M := M))
    (hParent : d.parent = gammaBall a ρ false) (hHoles : d.holes = {gammaBall c τ true})
    (hOpen : PaperBalls.IsOpenBall e.parent) (hEHoles : e.holes = {gammaBall k ν true})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body f))
    (hbij : Set.BijOn f d.body e.body) (hoo : MaximalOpenClasses.OpenToOpen d.body f) :
    ∃ J : Set (Values.Gamma (M := M)), (J = Set.Iic ν ∨ ∃ σ, J = Set.Ioc σ ν) ∧
      ∃ q : Set.Icc ρ τ → J, Function.Bijective q ∧
        FullGammaSyntax.Definable (RealParameterTuples.extend B ![c.val,k.val])
          (DefinableGammaMatching.graph (Set.Icc ρ τ) J q) := by
  have hD := RadialAnnulusDomains.punctured_closed d a c ρ τ hParent hHoles
  have hV : Values.infinity ∉ Set.Icc ρ.val τ.val := fun h => RadialValuePullbacks.infinity_not_Iic τ h.2
  rw [hD] at hf hbij hoo
  rcases hOpen with hVF | ⟨b,σ,hParentE⟩
  · have hE := RadialAnnulusDomains.punctured_whole_field e k ν hVF hEHoles
    rw [hE] at hbij
    have h := radial_to_gamma hκ hs h00 B hsmall c k (Set.Icc ρ.val τ.val) (Set.Iic ν.val)
      hV (RadialValuePullbacks.infinity_not_Iic ν) f hf hbij hoo
    exact ⟨Set.Iic ν,Or.inl rfl,h⟩
  · have hE := RadialAnnulusDomains.punctured_open e b k σ ν hParentE hEHoles
    rw [hE] at hbij
    have hW : Values.infinity ∉ Set.Ioc σ.val ν.val := fun h => RadialValuePullbacks.infinity_not_Iic ν h.2
    have h := radial_to_gamma hκ hs h00 B hsmall c k (Set.Icc ρ.val τ.val) (Set.Ioc σ.val ν.val)
      hV hW f hf hbij hoo
    exact ⟨Set.Ioc σ ν,Or.inr ⟨σ,rfl⟩,h⟩

end IntegrationInACVF.Section3ACVF.AnnulusGammaReduction
