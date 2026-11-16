module

public import Integration7.GammaTotalSupportedJacobianGraphs
public import Integration7.FiniteVolumeIsoMaps
public import Section9.GenericRVJacobian

@[expose] public section

/-! The checked GenericRVJacobian construction, with its original-Gamma
full graph retained. The finite chart support has no model parameters.
Construction and RV-dimension argument follow the pinned predecessor's
Section9/GenericRVJacobian.lean; Gamma graph tracking is supplied here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open FirstOrder FirstOrder.Language CategoryTheory MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M

private theorem supportedChartValues_relationDefinable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (C : DefSet (rawRVSpace (M := M) (n+n)) S) (A : Finset (VolumeChartSupport n)) :
    (rawRVSpace (M := M) (n+n)).RelationDefinable (rawRVSpace (M := M) 1) S
      (fun t ω => ∃ σ ∈ A, VolumeChartValue σ C.carrier t ω) := by
  classical
  let P := rawRVSpace (M := M) (n+n)
  let Q := rawRVSpace (M := M) 1
  induction A using Finset.induction_on with
  | empty =>
    apply ((P.definable_empty S).left_relation P Q).congr P Q
    simp
  | insert σ A hσ ih =>
    apply ((volumeChartValue_relationDefinable hc σ C).union P Q ih).congr P Q
    simp [Finset.mem_insert, or_and_right, exists_or]

theorem exists_gamma_generic_RVJacobian
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M) (hn : 0 < n)
    (PΓ : Base (M := M))
    {U V : RVFiniteObject (M := M) (B.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (Raw : Set (Fin (n+n) → M))
    (hRaw : DefinableOverBase PΓ (fun _ => .rv) Raw)
    (hRC : ∀ t, rvValues t ∈ Raw ↔ t ∈ (volumeCorrespondence (finiteIsoMap e)).carrier)
    (hPairΓ : GammaGraphDefinable PΓ
      (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 (n+n)) =>
        ∃ u : U.obj.domain, u.val = p.2 ∧ (volumePairMap (finiteIsoMap e) u).val = q.2)) :
    ∃ ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (B.base : Set M)),
      ∃ X : DefSet (rawRVSpace (M := M) U.obj.arity) (B.base : Set M),
        X.carrier ⊆ U.obj.domain.carrier ∧ rvDim X < n ∧
        (∀ u : U.obj.domain, u.val ∉ X.carrier → IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
          (U.obj.value u) (V.obj.value (finiteIsoMap e u)) ((ω u).val 0)) ∧
        GammaGraphDefinable PΓ (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 1) =>
          ∃ u : U.obj.domain, u.val = p.2 ∧ (ω u).val = q.2) := by
  let S := (B.base : Set M)
  let E := (finiteVolumeProperty S n).ι.mapIso e
  let C := volumeCorrespondence E.hom.map
  let P := rawRVSpace (M := M) (n+n)
  let Q := rawRVSpace (M := M) 1
  let f := volumePairMap E.hom.map
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed k := ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  obtain ⟨A, hA⟩ := exists_finite_volume_chart_cover hc B E
  let R (t : P.Carrier) (ω : Q.Carrier) := ∃ σ ∈ A, VolumeChartValue σ C.carrier t ω
  have hR : P.RelationDefinable Q S R := supportedChartValues_relationDefinable hc C A
  let D := C.sdiff ⟨{t | ∃ ω, R t ω}, hR.exists_right P Q⟩
  have hD₀ (t) (ht : t ∈ D.carrier) (i : Fin (n+n)) : (t i).val ≠ iRVZero := by
    obtain ⟨u, rfl⟩ := ht.1
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
    · change (productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) (productLeft n n j)).val ≠ iRVZero
      rw [productTuple_left]
      exact hU u j
    · change (productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) (productRight n n j)).val ≠ iRVZero
      rw [productTuple_right]
      exact hV (E.hom.map u) j
  have hd : rvDim D < n := by
    by_contra h
    have hh := (volumePair_leftProjection_finite E.hom.map U.property).restrict
      (show D.carrier ⊆ C.carrier from Set.diff_subset)
    have hd' : rvDim D = n := ((rvDim_le_of_finite_map _ hh).trans (rvDim_le_arity _)).antisymm
      (Nat.le_of_not_gt h)
    obtain ⟨p, hp, ω, σ, hσ, hJ⟩ := exists_chartValue_of_full_volumePair_dimension hc B hn
      E U.property A hA D Set.diff_subset hD₀ hd'
    exact hp.2 ⟨ω, σ, hσ, hJ⟩
  have hzero : Q.Definable S {ω | ω 0 = 0} := by
    have h := (Q.definable_domain S).inter (rvZero_coordinate_definable S (0 : Fin 1))
    change S.Definable LRV _
    convert h using 1
    ext z
    constructor
    · rintro ⟨hz, he⟩
      exact ⟨hz, (congrFun (rvValues_decode ⟨z, hz⟩) 0).symm.trans
        ((congrArg Subtype.val he).trans RVOperations.zero_val)⟩
    · rintro ⟨hz, he⟩
      exact ⟨hz, Subtype.ext ((congrFun (rvValues_decode ⟨z, hz⟩) 0).trans (he.trans RVOperations.zero_val.symm))⟩
  let T (t : P.Carrier) (ω : Q.Carrier) := t ∈ C.carrier ∧ (R t ω ∨ (t ∈ D.carrier ∧ ω 0 = 0))
  have hT : P.RelationDefinable Q S T := (C.definable.left_relation P Q).inter P Q
    (hR.union P Q ((D.definable.left_relation P Q).inter P Q (hzero.right_relation P Q)))
  have hdom t ω (h : T t ω) : t ∈ C.carrier ∧ ω ∈ (DefSet.univ Q S).carrier := ⟨h.1, Set.mem_univ _⟩
  have htotal (t : C) : ∃ ω, T t.val ω := by
    by_cases ht : ∃ ω, R t.val ω
    · obtain ⟨ω, hω⟩ := ht
      exact ⟨ω, t.property, Or.inl hω⟩
    · exact ⟨fun _ => 0, t.property, Or.inr ⟨⟨t.property, ht⟩, rfl⟩⟩
  have huniq t ω η (hω : T t ω) (hη : T t η) : ω = η := by
    have he : ω 0 = η 0 := by
      rcases hω.2 with ⟨σ, hσ, hj⟩ | hω
      · rcases hη.2 with ⟨τ, hτ, hj'⟩ | hη
        · exact hj.isRVJacobianAt.unique hj'.isRVJacobianAt
        · exact (hη.1.2 ⟨ω, σ, hσ, hj⟩).elim
      · rcases hη.2 with hη | hη
        · exact (hω.1.2 ⟨η, hη⟩).elim
        · exact hω.2.trans hη.2.symm
    funext i
    fin_cases i
    exact he
  let j : Map C (DefSet.univ Q S) := Map.ofFunctionalRelation hT hdom htotal huniq
  let X := U.obj.domain.sdiff ⟨{t | ∃ u : U.obj.domain, u.val = t ∧ (f u).val ∉ D.carrier},
    f.definable_preimage (D.definable.compl P)⟩
  let f' := f.restrict (show X.carrier ⊆ U.obj.domain.carrier from Set.diff_subset)
  let g := f'.corestrict
    (fun x => by
      by_contra h
      exact x.property.2 ⟨⟨x.val, x.property.1⟩, rfl, h⟩)
  have hg : g.FiniteFibres := by
    intro z
    let q : C := ⟨z.val, z.property.1⟩
    apply (((volumePairMap_finite E.hom.map U.property).restrict
      (show X.carrier ⊆ U.obj.domain.carrier from Set.diff_subset)) q).subset
    intro x hx
    have he := congrArg Subtype.val hx
    exact Subtype.ext he
  have hTotalΓ := gamma_total_supported_jacobian_graph hc A C.carrier Raw hRaw hRC
  have hMapΓ : GammaGraphDefinable PΓ
      (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 1) =>
        ∃ u : U.obj.domain, u.val = p.2 ∧ ((j.comp f) u).val = q.2) := by
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr
      ((gammaLogicInput PΓ).comp_graph hPairΓ hTotalΓ)
    intro p q
    constructor
    · rintro ⟨t,⟨u,hu,hpair⟩,hval⟩
      have hv : totalSupportedJacobianGraph A C.carrier (f u).val q.2 :=
        (congrArg (fun r : Fin (n+n) → RV => totalSupportedJacobianGraph A C.carrier r q.2) hpair).mpr hval
      have ht : T (f u).val q.2 := by
        refine ⟨hv.1,?_⟩
        rcases hv.2 with hj | hj
        · exact Or.inl hj
        · exact Or.inr ⟨⟨hv.1,hj.1⟩,hj.2⟩
      exact ⟨u,hu,huniq _ _ _ (Map.ofFunctionalRelation_graph hT hdom htotal huniq (f u)) ht⟩
    · rintro ⟨u,hu,hq⟩
      refine ⟨(Fin.elim0,(f u).val),⟨u,hu,rfl⟩,?_⟩
      have ht := Map.ofFunctionalRelation_graph hT hdom htotal huniq (f u)
      have hv : totalSupportedJacobianGraph A C.carrier (f u).val (j (f u)).val := by
        refine ⟨ht.1,?_⟩
        rcases ht.2 with hj | hj
        · exact Or.inl hj
        · exact Or.inr ⟨hj.1.2,hj.2⟩
      exact (congrArg (fun r : Fin 1 → RV => totalSupportedJacobianGraph A C.carrier (f u).val r) hq).mp hv
  refine ⟨j.comp f, X, Set.diff_subset, (rvDim_le_of_finite_map g hg).trans_lt hd, ?_,hMapΓ⟩
  intro u hu
  have hnot : (f u).val ∉ D.carrier := by
    intro h
    exact hu ⟨u.property, fun h' => by
      obtain ⟨v, he, hv⟩ := h'
      exact hv (Subtype.ext he ▸ h)⟩
  have h := Map.ofFunctionalRelation_graph hT hdom htotal huniq (f u)
  rcases h.2 with ⟨σ, hσ, hJ⟩ | h
  · have he : (f u).val = productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) :=
      volumePairMap_apply E.hom.map u
    have hl : (f u).val ∘ productLeft n n = U.obj.value u := by
      rw [he]
      exact funext (productTuple_left _ _)
    have hr : (f u).val ∘ productRight n n = V.obj.value (E.hom.map u) := by
      rw [he]
      exact funext (productTuple_right _ _)
    have hj := hJ.isRVJacobianAt
    rw [hl, hr] at hj
    exact hj
  · exact (hnot h.1).elim

end IntegrationInACVF.Section7
