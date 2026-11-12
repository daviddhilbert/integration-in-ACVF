import IntegrationSection6.GammaSchemaFiniteRows
import IntegrationSection6.GammaRawCoproductSchemaBridge
import IntegrationSection6.GammaRawElementarySchemaBridge

/-! Bound-independent finite rows have actual native finite graph
presentations. Native coproducts and admissible elementary blowups preserve
these rows without asserting a common numerical bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaFiniteRVSchema.realize_finiteRow (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j)) (hF : F.finiteRow z) :
    Nonempty (GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) := by
  have hD := gamma_rv_set_from_tuple_formula
    (gamma_tuple_parameter_specialize sp (fun _ : Fin a => .rv) z F.domain_definable)
  have hV := gamma_rv_tuple_relation_specialize sp z hz F.volume_definable
  apply exists_gammaFiniteGraphPresentation hD hV (fun x => hF.1 x.val x.property)
  intro y
  apply (hF.2.2 y).of_injOn (f := fun x : F.rowDomain z => x.val)
  · exact fun x hx => hx
  · exact fun x hx x' hx' he => Subtype.ext he

theorem GammaFiniteRVSchema.finiteRow_of_presentation (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hsupport : ∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) : F.finiteRow z := by
  refine ⟨?_,hsupport,?_⟩
  · intro x hx
    let u : P.domain := ⟨x,(Set.ext_iff.mp P.domain_eq x).mpr hx⟩
    refine ⟨(P.volume u).val,((P.graph_iff x (P.volume u).val).mp ⟨u,rfl,rfl⟩).2,?_⟩
    intro y hy
    obtain ⟨v,hv,hvy⟩ := (P.graph_iff x y).mpr ⟨hx,hy⟩
    have he : v = u := Subtype.ext hv
    exact (he ▸ hvy).symm
  · intro y
    have h := (P.finite_volume ⟨y,Set.mem_univ _⟩).image (fun u : P.domain => u.val)
    apply h.subset
    intro x hx
    obtain ⟨u,hu,hy⟩ := (P.graph_iff x y).mpr ⟨hsupport x y hx,hx⟩
    exact ⟨u,Subtype.ext hy,hu⟩

theorem GammaFiniteRVSchema.finiteRow_coprod (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : F.finiteRow z) (hG : G.finiteRow z) : (F.coprodFormula G).finiteRow z := by
  obtain ⟨P⟩ := F.realize_finiteRow z hz hF
  obtain ⟨Q⟩ := G.realize_finiteRow z hz hG
  exact (F.coprodFormula G).finiteRow_of_presentation z
    (F.coprod_row_support G z hz hF.2.1 hG.2.1)
    (F.coprodPresentation G z hz hF.2.1 hG.2.1 P Q)

theorem GammaFiniteAdmissibilitySchema.elementary_finiteRow {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (F : GammaFiniteAdmissibilitySchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) : (F.object.elementaryFormula F.coordinate).finiteRow z := by
  obtain ⟨P⟩ := F.object.realize z hz.1
  let E := F.object.elementaryPresentation hκ hs h00 hreal z hz.1.1 P F.coordinate (F.admissible z hz P)
  exact (F.object.elementaryFormula F.coordinate).finiteRow_of_presentation z
    (F.object.elementary_row_support F.coordinate z hz.1.1) E

end IntegrationInACVF.Section6
