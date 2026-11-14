import Integration7.RawRVRelationFormulas
import Integration7.CanonicalRawGammaFormulas
import IntegrationSection6.GammaFiniteGraphObjects
import IntegrationSection6.GammaRawRVFormulas

/-! An actual finite RV map whose complete raw formulas descend to a
specified real base has a full Gamma presentation over precisely that
base. This will encode exceptional maps after naming auxiliary parameters. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {a j : ℕ}

theorem realFiniteMap_gammaPresentation
    (hc : CanonicalStructure.IsCanonical (M := M))
    (D : DefSet (rawRVSpace (M := M) a) S)
    (g : Map D (DefSet.univ (rawRVSpace (M := M) j) S)) (hg : g.FiniteFibres)
    (hD : B.real.Definable LRV ((rawRVSpace (M := M) a).preimage D.carrier))
    (hG : B.real.Definable LRV (rawRVRelationFormula g.graph)) :
    Nonempty (GammaFiniteGraphPresentation B a j D.carrier g.graph) := by
  have hDproper : ∀ w ∈ (rawRVSpace (M := M) a).preimage D.carrier, ∀ i, sortEval SortTag.rv (w i) := by
    rintro w ⟨hw,_⟩ i
    obtain ⟨x,rfl⟩ := hw
    exact (x i).property
  have hDraw := canonicalRawGammaFormula hc B (fun _ : Fin a => .rv) hD hDproper
  have hDΓ : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ D.carrier} := by
    have h := gamma_rv_set_from_tuple_formula hDraw
    convert h using 1
    ext p
    have he := Space.preimage_decode (rawRVSpace (M := M) a) D.carrier ⟨rvValues p.2,⟨p.2,rfl⟩⟩
    simp only [decode_rvValues] at he
    change (rvValues p.2 ∈ (rawRVSpace (M := M) a).preimage D.carrier) ↔ p.2 ∈ D.carrier at he
    change (p.2 ∈ D.carrier) ↔ rvValues p.2 ∈ (rawRVSpace (M := M) a).preimage D.carrier
    exact he.symm
  have hGraw := canonicalRawGammaFormula hc B (fun _ : Fin (a+j) => .rv) hG
    (fun w hw i => rawRVRelationFormula_proper g.graph w hw i)
  have hGΓ : GammaGraphDefinable B
      (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 j) => g.graph x.2 y.2) :=
    GammaGraphDefinable.congr (gamma_rv_graph_from_tuple_formula hGraw)
      (fun x y => rawRVRelationFormula_append g.graph x.2 y.2)
  apply exists_gammaFiniteGraphPresentation hDΓ hGΓ
  · intro x
    refine ⟨(g x).val,⟨x,rfl,rfl⟩,?_⟩
    intro y hy
    exact ((Map.graph_apply g x y).mp hy).symm
  · intro y
    apply (hg ⟨y,Set.mem_univ _⟩).subset
    intro x hx
    apply Subtype.ext
    exact (Map.graph_apply g x y).mp hx

end IntegrationInACVF.Section7
