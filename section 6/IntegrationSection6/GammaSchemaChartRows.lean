import IntegrationSection6.GammaIsomorphismRealization
import IntegrationSection6.GammaRelationalIsoSpecification
import IntegrationSection6.GammaIndexedIsomorphisms

/-! Valid chart rows give actual original-Gamma isomorphisms of RV[k]
objects, including both inherited finite volume-image conditions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaFiniteRVIsoSchema.realizeChart_apply (F : GammaFiniteRVIsoSchema B p a b k sp)
    (z : Fin p → M) (hz : F.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.source.rowDomain z) (F.source.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (F.target.rowDomain z) (F.target.rowVolume z))
    (u : P.domain) :
    Fin.append (Fin.append z (fun j => (u.val j).val))
      (fun j => (((F.realizeChart z hz P Q).equiv u).val j).val) ∈ F.chart := by
  unfold GammaFiniteRVIsoSchema.realizeChart
  dsimp only
  exact FiniteRV.gammaIsoOfFiniteRelation_apply P.toGamma Q.toGamma
    (fun x y => Fin.append (Fin.append z (fun j => (x j).val)) (fun j => (y j).val) ∈ F.chart)
    _ _ _ _ _ _ u

def GammaFiniteRVIsoSchema.rowEquiv (F : GammaFiniteRVIsoSchema B p a b k sp)
    (z : Fin p → M) (hz : F.valid z) : F.source.rowDomain z ≃ F.target.rowDomain z :=
  let P := Classical.choice (F.source.realize z hz.1)
  let Q := Classical.choice (F.target.realize z hz.2.1)
  P.domainEquiv.symm.trans ((F.realizeChart z hz P Q).equiv.trans Q.domainEquiv)

theorem GammaFiniteRVIsoSchema.rowEquiv_apply (F : GammaFiniteRVIsoSchema B p a b k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.source.rowDomain z) :
    Fin.append (Fin.append z (fun j => (x.val j).val))
      (fun j => ((F.rowEquiv z hz x).val j).val) ∈ F.chart :=
  F.realizeChart_apply z hz (Classical.choice (F.source.realize z hz.1))
    (Classical.choice (F.target.realize z hz.2.1))
    ((Classical.choice (F.source.realize z hz.1)).domainEquiv.symm x)

theorem GammaFiniteRVIsoSchema.rowEquiv_graph (F : GammaFiniteRVIsoSchema B p a b k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.source.rowDomain z) (y : F.target.rowDomain z) :
    Fin.append (Fin.append z (fun j => (x.val j).val)) (fun j => (y.val j).val) ∈ F.chart ↔
      F.rowEquiv z hz x = y := by
  constructor
  · intro hxy
    have hu := hz.2.2.1.1.2.1 (fun j => (x.val j).val) x.property
    have he := hu.unique (F.rowEquiv_apply z hz x) hxy
    apply Subtype.ext
    funext j
    exact Subtype.ext (congrFun he j)
  · intro hxy
    rw [← hxy]
    exact F.rowEquiv_apply z hz x

end IntegrationInACVF.Section6
