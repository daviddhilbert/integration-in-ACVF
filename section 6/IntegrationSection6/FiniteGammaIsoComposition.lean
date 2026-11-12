import IntegrationSection6.GammaFiniteGraphIsomorphisms

/-! Composition and inversion of actual finite Gamma RV isomorphisms,
retaining full original-base graphs and inherited finite volume images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def gammaFiniteIsoTrans (U V W : GammaRVFiniteObject B k)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (f : GammaRVIso V.toGammaRVObject W.toGammaRVObject) :
    GammaRVIso U.toGammaRVObject W.toGammaRVObject := by
  refine gammaIsoOfFiniteEquiv U W (e.equiv.trans f.equiv) ?_ (fun u => (e.weight u).trans (f.weight (e.equiv u)))
  apply GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph e.graph f.graph)
  intro p q
  constructor
  · rintro ⟨z,⟨u,hu,hz⟩,⟨v,hv,hq⟩⟩
    have he : v = e.equiv u := Subtype.ext (hv.trans hz.symm)
    exact ⟨u,hu,(congrArg (fun x => (f.equiv x).val) he).symm.trans hq⟩
  · rintro ⟨u,hu,hq⟩
    exact ⟨(Fin.elim0,(e.equiv u).val),⟨u,hu,rfl⟩,⟨e.equiv u,rfl,hq⟩⟩

def gammaFiniteIsoSymm (U V : GammaRVFiniteObject B k)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    GammaRVIso V.toGammaRVObject U.toGammaRVObject := by
  refine gammaIsoOfFiniteEquiv V U e.equiv.symm ?_ ?_
  · apply GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph e.graph)
    intro p q
    constructor
    · rintro ⟨u,hu,hv⟩
      exact ⟨e.equiv u,hv,by simpa only [Equiv.symm_apply_apply] using hu⟩
    · rintro ⟨v,hv,hu⟩
      exact ⟨e.equiv.symm v,hu,by simpa only [Equiv.apply_symm_apply] using hv⟩
  · intro v
    simpa only [Equiv.apply_symm_apply] using (e.weight (e.equiv.symm v)).symm

end IntegrationInACVF.Section6.FiniteRV
