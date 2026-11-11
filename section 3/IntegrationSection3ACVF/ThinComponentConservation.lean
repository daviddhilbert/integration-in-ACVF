import IntegrationSection3ACVF.RVQuotientGraph
import IntegrationSection3ACVF.FiniteFamilyMaximal
import IntegrationSection3ACVF.ResidueTaggedConservation
import IntegrationSection3.SurjectiveQuotientMap

/-! Component and hole conservation for finite actual thin families in
a canonical model. The full original partial VF graph is the definability
input; the induced RV graph and quotient bijection are proved here. The
canonical-to-general-model transport remains a separate bridge. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open scoped BigOperators
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
open IntegrationInACVF.Section3ACVF.ThinResidueCoordinates

noncomputable section

namespace IntegrationInACVF.Section3ACVF.ThinComponentConservation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem canonical (hc : CanonicalStructure.IsCanonical (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (F G : Finset (PuncturedBall M)) (hThinF : ∀ d ∈ F, IsThin d) (hThinG : ∀ d ∈ G, IsThin d)
    (hF : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (hG : (G : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (f : M → M)
    (hf : (Set.univ : Set M).Definable LRV {z : Fin 2 → M | z 0 ∈ body F ∧ z 1 = f (z 0)})
    (hbij : Set.BijOn f (body F) (body G)) (hoo : MaximalOpenClasses.OpenToOpen (body F) f) :
    F.card = G.card ∧ (∑ d : F, d.val.holes.card) = ∑ d : G, d.val.holes.card := by
  classical
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  letI : Inhabited (ModelResidue M) := ⟨0⟩
  let C : ∀ d : F, Chart d.val := fun d => Classical.choice (exists_chart d.val (hThinF d.val d.property))
  let D : ∀ d : G, Chart d.val := fun d => Classical.choice (exists_chart d.val (hThinG d.val d.property))
  let nt := Infinite.natEmbedding (ModelResidue M)
  let e : F ↪ ModelResidue M := ⟨fun d => nt ((Fintype.equivFin F) d).val,
    fun x y he => (Fintype.equivFin F).injective (Fin.ext (nt.injective he))⟩
  let k : G ↪ ModelResidue M := ⟨fun d => nt ((Fintype.equivFin G) d).val,
    fun x y he => (Fintype.equivFin G).injective (Fin.ext (nt.injective he))⟩
  let p := FiniteFamilyCoordinates.value F C e
  let q := FiniteFamilyCoordinates.value G D k
  let P := FiniteTaggedHoles.tags e
  let Q := FiniteTaggedHoles.tags k
  let H := FiniteTaggedHoles.holes e (fun d => (C d).excluded)
  let J := FiniteTaggedHoles.holes k (fun d => (D d).excluded)
  let U := TaggedLineMaps.space P \ H
  let V := TaggedLineMaps.space Q \ J
  have hp : (body F).MapsTo p U ∧ (body F).SurjOn p U :=
    FiniteFamilyCoordinates.cofinite_image F C e hF
  have hq : (body G).MapsTo q V ∧ (body G).SurjOn q V :=
    FiniteFamilyCoordinates.cofinite_image G D k hG
  have hpMax (x : M) (hx : x ∈ body F) := FiniteFamilyMaximal.fibre_maximal δ hδ F C e hF x hx
  have hqMax (y : M) (hy : y ∈ body G) := FiniteFamilyMaximal.fibre_maximal δ hδ G D k hG y hy
  have hker (x : M) (hx : x ∈ body F) (y : M) (hy : y ∈ body F) : p x = p y ↔ q (f x) = q (f y) :=
    OpenToOpenQuotient.same_fibres f hbij hoo p q hpMax hqMax x y hx hy
  obtain ⟨g,hg,_,hFull⟩ := SurjectiveQuotientMap.exists_bijective_factor f hbij p q hp hq hker
  let R := RVQuotientGraph.relation (FiniteFamilySyntax.graph F C e) (FiniteFamilySyntax.graph G D k)
    {z : Fin 2 → M | z 0 ∈ body F ∧ z 1 = f (z 0)}
  have hR : (Set.univ : Set M).Definable LRV R := RVQuotientGraph.relation_definable Set.univ
    (FiniteFamilySyntax.graph_definable hc F C e) (FiniteFamilySyntax.graph_definable hc G D k) hf
  let A := RVQuotientGraph.ofRaw Set.univ R hR
  have hGraph (u v : Fin 2 → ModelResidue M) :
      (Fin.addCases (fun i => residueRV (u i)) (fun i => residueRV (v i)) :
        Fin (2+2) → CanonicalRV.RVSort M) ∈ A.carrier ↔ u ∈ U ∧ v = g u := by
    change rvValues (Fin.addCases (fun i => residueRV (u i)) (fun i => residueRV (v i)) : Fin (2+2) → CanonicalRV.RVSort M) ∈ R ↔ _
    have he : rvValues (Fin.addCases (fun i => residueRV (u i)) (fun i => residueRV (v i)) : Fin (2+2) → CanonicalRV.RVSort M) =
        (![(residueRV (u 0)).val,(residueRV (u 1)).val,(residueRV (v 0)).val,(residueRV (v 1)).val] : Fin 4 → M) := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact (RVQuotientGraph.relation_iff F G C D e k hF hG f hbij.1 u v).trans (hFull u v).symm
  have hCounts := ResidueTaggedConservation.components_and_holes hc A P Q H J
    (FiniteTaggedHoles.holes_subset e (fun d => (C d).excluded))
    (FiniteTaggedHoles.holes_subset k (fun d => (D d).excluded)) g hGraph hg
  have hCF := FiniteFamilyMaximal.counts F C e
  have hCG := FiniteFamilyMaximal.counts G D k
  exact ⟨hCF.1.symm.trans (hCounts.1.trans hCG.1),hCF.2.symm.trans (hCounts.2.trans hCG.2)⟩

end IntegrationInACVF.Section3ACVF.ThinComponentConservation
