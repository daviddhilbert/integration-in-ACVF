import IntegrationSection6.FiniteGammaIsomorphisms
import IntegrationSection6.GammaRVGlobalRestriction

/-! Isomorphism laws in the original-Gamma finite RV categories, retaining
the full label graphs. Finite volume-image fields are derived from RV[k]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaIsoRefl (U : GammaRVFiniteObject B n) : GammaRVIso U.toGammaRVObject U.toGammaRVObject :=
  gammaIsoOfFiniteEquiv U U (Equiv.refl _) (by
    apply gamma_rv_graph_of_global_formula
      (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ U.codes (rvObjectDomain U.object))
      (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real
        (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
          (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object)) B.real)) U.domain_graph
    intro u
    rfl) (fun _ => rfl)

def gammaIsoSymm {U V : GammaRVFiniteObject B n} (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    GammaRVIso V.toGammaRVObject U.toGammaRVObject :=
  gammaIsoOfFiniteEquiv V U e.equiv.symm (by
    apply GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph e.graph)
    intro q p
    constructor
    · rintro ⟨u,hu,he⟩
      exact ⟨e.equiv u,he,by simpa only [Equiv.symm_apply_apply] using hu⟩
    · rintro ⟨v,hv,hp⟩
      exact ⟨e.equiv.symm v,hp,(congrArg Subtype.val (e.equiv.apply_symm_apply v)).trans hv⟩) (by
    intro v
    have h := e.weight (e.equiv.symm v)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm)

def gammaIsoTrans {U V W : GammaRVFiniteObject B n}
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (f : GammaRVIso V.toGammaRVObject W.toGammaRVObject) :
    GammaRVIso U.toGammaRVObject W.toGammaRVObject :=
  gammaIsoOfFiniteEquiv U W (e.equiv.trans f.equiv) (by
    apply GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph e.graph f.graph)
    intro p q
    constructor
    · rintro ⟨z,⟨u,hu,hz⟩,⟨v,hv,hq⟩⟩
      have he : v = e.equiv u := Subtype.ext (hv.trans hz.symm)
      exact ⟨u,hu,(congrArg (fun v => (f.equiv v).val) he).symm.trans hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨(Fin.elim0,(e.equiv u).val),⟨u,hu,rfl⟩,⟨e.equiv u,rfl,hq⟩⟩) (by
    intro u
    exact (e.weight u).trans (f.weight (e.equiv u)))

end IntegrationInACVF.Section6.FiniteRV
