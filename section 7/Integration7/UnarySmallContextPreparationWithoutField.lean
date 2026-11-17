module

public import Integration7.UnarySmallContextPreparation
public import Integration7.VFFieldContainingVolumeContexts
public import IntegrationSection6.GammaSpecialBaseReduction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Unary preparation over an arbitrary real/Gamma base. An internal
coefficient field is contained in a small context; definable-name
elimination returns every special chain and graph to the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem unary_bijection_preparation_in_context_without_field
    (C : BaseContext M) (P : GammaParameters.Base (M := M))
    (hPC : P.real ⊆ (C.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ P.gamma) (hδ1 : 1 < δ) {m l : ℕ}
    {A : DefSet (M := M) (C.base : Set M) 1 m}
    {B : DefSet (M := M) (C.base : Set M) 1 l}
    (f : Map A B) (hf : Function.Bijective f)
    (hADef : GammaSetDefinable P (carrier A))
    (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) (D.base : Set M) 1 r,
      ∃ B' : DefSet (M := M) (D.base : Set M) 1 s,
      ∃ TA : SpecialBijection (extendBase A hCD) A',
      ∃ TB : SpecialBijection (extendBase B hCD) B',
        let fD := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
          (@CanonicalStructure.normalize M sM) (pointSpace 1 m) (pointSpace 1 l)
          (C.base : Set M) (D.base : Set M) A B f hCD
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (unaryConjugate TA TB fD) ∧
        Contractible (Map.inverse (unaryConjugate TA TB fD)
          (unaryConjugate_bijective TA TB fD hf)) ∧
        GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB fD)) ∧
        ∃! g : Map (keyImage A') (keyImage B'), Function.Bijective g ∧
          ∀ a : A', g (toKeyImage A' a) = toKeyImage B' (unaryConjugate TA TB fD a) := by
  let E := vfFieldContainingVolumeContext C P hPC
  have hCE : (C.base : Set M) ⊆ (E.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C P hPC (Or.inl hx)
  have hPE : (vfFieldNamedBase P).real ⊆ (E.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C P hPC (Or.inr hx)
  let fE : Map (extendBase A hCE) (extendBase B hCE) :=
    @SpecialTransformations.DefinableGeometry.Map.extend LRV M (@CanonicalStructure.normalize M sM)
      (pointSpace 1 m) (pointSpace 1 l) (C.base : Set M) (E.base : Set M) A B f hCE
  obtain ⟨D,hED,r,s,A',B',TA,TB,hTA,hTB,hA',hB',hcon,hback,hg,hkey⟩ :=
    unary_bijection_preparation_in_context E (vfFieldNamedBase P) hPE δ hδ hδ1
      (vfFieldNamedBase_field P) fE hf
      (hADef.mono Set.subset_union_left (Set.Subset.refl _))
      (hBDef.mono Set.subset_union_left (Set.Subset.refl _))
      (hfDef.mono Set.subset_union_left (Set.Subset.refl _))
  let H := vfFieldBaseReduction P
  exact ⟨D,hCE.trans hED,r,s,A',B',TA,TB,H.chainDefinable TA.chain hTA,
    H.chainDefinable TB.chain hTB,hA',hB',hcon,hback,H.definable hg,hkey⟩

end IntegrationInACVF.Section7
