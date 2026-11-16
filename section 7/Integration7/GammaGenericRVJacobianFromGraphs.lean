module

public import Integration7.GammaVolumePairGraphs
public import IntegrationSection6.GammaNativeRawObjects

@[expose] public section

/-! Original-Gamma coordinate and label graphs supply the raw
correspondence certificate needed by the Gamma generic-Jacobian theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable GammaSetDefinable gammaLogicInput gammaPointSort gammaPointCode)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a n : ℕ}

theorem gamma_raw_rv_carrier_definable
    (C : Set (Fin a → CanonicalRV.RVSort M))
    (hC : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ C}) :
    DefinableOverBase B (fun _ => .rv) {x | ∃ t ∈ C, rvValues t = x} := by
  have h := DefinableOverBase.image_real hC (Fin.natAdd 0)
  have hs : gammaPointSort 0 a ∘ Fin.natAdd 0 = (fun _ => SortTag.rv) := by
    funext j
    simp only [gammaPointSort,Function.comp_apply,Fin.append_right]
  rw [hs] at h
  convert h using 1
  ext x
  constructor
  · rintro ⟨t,ht,he⟩
    let p : Point (M := M) 0 a := (Fin.elim0,t)
    refine ⟨gammaPointCode p,⟨p,ht,rfl⟩,?_⟩
    have hv : gammaPointCode p ∘ Fin.natAdd 0 = rvValues t := by
      funext j
      unfold gammaPointCode
      change Fin.append _ _ (Fin.natAdd 0 j) = _
      rw [Fin.append_right]
      rfl
    exact hv.trans he
  · rintro ⟨z,⟨p,hp,rfl⟩,he⟩
    refine ⟨p.2,hp,?_⟩
    have hv : rvValues p.2 = gammaPointCode p ∘ Fin.natAdd 0 := by
      funext j
      unfold gammaPointCode
      change _ = Fin.append _ _ (Fin.natAdd 0 j)
      rw [Fin.append_right]
      rfl
    exact hv.trans he

theorem exists_gamma_generic_RVJacobian_of_graphs
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    (B : Base (M := M)) {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU0 : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV0 : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hU : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 n) =>
      U.obj.volume.graph p.2 q.2))
    (hV : GammaGraphDefinable B (fun (p : Point (M := M) 0 V.obj.arity) (q : Point (M := M) 0 n) =>
      V.obj.volume.graph p.2 q.2))
    (he : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 V.obj.arity) =>
      ∃ u : U.obj.domain, u.val = p.2 ∧ (finiteIsoMap e u).val = q.2)) :
    ∃ ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)),
      ∃ X : DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M),
        X.carrier ⊆ U.obj.domain.carrier ∧ rvDim X < n ∧
        (∀ u : U.obj.domain, u.val ∉ X.carrier → IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
          (U.obj.value u) (V.obj.value (finiteIsoMap e u)) ((ω u).val 0)) ∧
        GammaGraphDefinable B (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 1) =>
          ∃ u : U.obj.domain, u.val = p.2 ∧ (ω u).val = q.2) := by
  have hPair := gamma_volume_pair_graph e hU hV he
  have hDomain := gamma_volume_correspondence_domain e hPair
  let D := (volumeCorrespondence (finiteIsoMap e)).carrier
  let R : Set (Fin (n+n) → M) := {x | ∃ t ∈ D, rvValues t = x}
  have hR : DefinableOverBase B (fun _ => .rv) R := gamma_raw_rv_carrier_definable D hDomain
  have hRD : ∀ t, rvValues t ∈ R ↔ t ∈ D := by
    intro t
    constructor
    · rintro ⟨s,hs,he⟩
      exact rvValues_injective he ▸ hs
    · exact fun ht => ⟨t,ht,rfl⟩
  exact exists_gamma_generic_RVJacobian hc C hn B e hU0 hV0 R hR hRD hPair

end IntegrationInACVF.Section7
