import IntegrationSection5.UnaryRVIsomorphism
import IntegrationSection5.RVContractionGamma

/-! Lemma5.3 for the actual mutually contractible map furnished by Lemma5.2.
The morphisms belong to the unchanged RV[1,·] category and keep their full
original-Gamma graphs in both directions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

def rvPullbackMapGraph {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (g : Map (rvObjectDomain (pullbackObject A)) (rvObjectDomain (pullbackObject B)))
    (p : Point (M := M) 0 (n+m)) (q : Point (M := M) 0 (n+l)) : Prop :=
  ∃ u : rvObjectDomain (pullbackObject A), u.val = p.2 ∧ (g u).val = q.2

def unaryIsoHomMap (e : pullbackObject A ≅ pullbackObject B) :
    Map (rvObjectDomain (pullbackObject A)) (rvObjectDomain (pullbackObject B)) :=
  @SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM) S 1
    (@pullbackObject M sM hM S 1 m A) (@pullbackObject M sM hM S 1 l B) e.hom

def unaryIsoInvMap (e : pullbackObject A ≅ pullbackObject B) :
    Map (rvObjectDomain (pullbackObject B)) (rvObjectDomain (pullbackObject A)) :=
  @SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM) S 1
    (@pullbackObject M sM hM S 1 l B) (@pullbackObject M sM hM S 1 m A) e.inv

theorem lemma_5_3 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    ∃ e : pullbackObject A ≅ pullbackObject B,
      (∀ a : A, unaryIsoHomMap e (Map.toImage (rawKeyMap A) a) = Map.toImage (rawKeyMap B) (f a)) ∧
      GammaGraphDefinable P (rvPullbackMapGraph (unaryIsoHomMap e)) ∧
      GammaGraphDefinable P (rvPullbackMapGraph (unaryIsoInvMap e)) := by
  refine ⟨unaryRVIso hκ hs hsmall f hf hc hback hA hB hfDef,?_,?_,?_⟩
  · exact unaryRVIso_spec hκ hs hsmall f hf hc hback hA hB hfDef
  · exact gamma_rvContractionMap_graph f hc hfDef
  · exact gamma_rvContractionMap_graph (Map.inverse f hf) hback (gamma_inverse_map_graph f hf hfDef)

end IntegrationInACVF.Section5
