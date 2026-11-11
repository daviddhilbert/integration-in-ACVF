import Section5.GammaInvariantLogic

/-! Prepare a relation uniformly in every free RV variable, over the original
Gamma-named base. We reuse the predecessor's finite polynomial support and
actual special-bijection preparation. Restriction retains the invariant
primitive graphs and the complete original domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaRelationPreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m k : ℕ}

theorem prepare_with_inputs {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v G.real N)
    (hΓ : GammaLogicInput G) (hSupport : GammaPolynomialSupportInput G)
    (hGS : G.real ⊆ S) (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable G (carrier A))
    (r : Point (M := M) n m → Point (M := M) 0 k → Prop)
    (hr : GammaGraphDefinable G r) (previous : Option Bool)
    (hTags : previous = some false → AllTagged A) :
    ∃ l : ℕ, ∃ D : DefSet (M := M) S n l, ∃ U : SpecialBijection A D,
      U.chain.Alternating previous ∧ GammaChainDefinable G U.chain ∧
        IsRVPullback (carrier D) ∧ ∀ b c : D, SameRV b.val c.val →
          ∀ z, r (U.inverseMap b).val z ↔ r (U.inverseMap c).val z := by
  let domain : Point (M := M) n m → Point (M := M) 0 0 → Prop := fun p _ => p ∈ carrier A
  have hDomain : GammaGraphDefinable G domain := by
    have hd := hΓ.restrict_graph hA (hΓ.real_map_graph
      (constantRVMap (PresentedSet.univ (pointSpace n m) G.real) 0))
    apply GammaGraphDefinable.congr hd
    intro p q
    constructor
    · exact fun h => h.1
    · intro hp
      exact ⟨hp, ⟨p, Set.mem_univ _⟩, rfl, Subsingleton.elim _ _⟩
  obtain ⟨dA,pA,hcoeffA,hcontrolA⟩ := hSupport domain hDomain
  obtain ⟨dR,pR,hcoeffR,hcontrolR⟩ := hSupport r hr
  let p := Fin.append pA pR
  have hcoeff : ∀ i e, ((p i).coeff e).val ∈ G.real := by
    intro i e
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [p,Fin.append_left] using hcoeffA j e
    · simpa only [p,Fin.append_right] using hcoeffR j e
  have hAmbient : ∃ E : DefSet (M := M) G.real n m,
      carrier A ⊆ carrier E ∧ (previous = some false → AllTagged E) := by
    by_cases hp : previous = some false
    · obtain ⟨E,hAE,hEt,_⟩ := exists_taggedAmbient (S := G.real) (carrier A) (hTags hp)
      exact ⟨E,hAE,fun _ => hEt⟩
    · exact ⟨PresentedSet.univ (pointSpace n m) G.real,Set.subset_univ _,fun h => (hp h).elim⟩
  obtain ⟨E,hAE,hEt⟩ := hAmbient
  let g := mvPolynomialTupleMap E p hcoeff
  obtain ⟨l,C,T,hTa,hC,hg⟩ := map_preparation_at_boundary h00 v hv hObstacles previous hEt g
  let W := T.extendBase hGS
  have hWa := T.chain.extendBase_alternating hGS previous hTa
  have hWG : GammaChainDefinable G W.chain :=
    GammaChainDefinable.extendBase G T.chain hGS (GammaChainDefinable.of_real hΓ T.chain)
  have hPoly (b c : extendBase C hGS) (he : SameRV b.val c.val) :
      ∀ i, rv (MvPolynomial.eval (vfAt (W.inverseMap b).val) (p i)) =
        rv (MvPolynomial.eval (vfAt (W.inverseMap c).val) (p i)) := by
    intro i
    let b₀ : C := ⟨b.val,b.property⟩
    let c₀ : C := ⟨c.val,c.property⟩
    have hh := ((sameRV_iff _ _).mp (hg b₀ c₀ he)).1 i
    change rv (MvPolynomial.eval (vfAt (T.inverseMap b₀).val) (p i)) =
      rv (MvPolynomial.eval (vfAt (T.inverseMap c₀).val) (p i)) at hh
    exact (congrArg (fun z : Point (M := M) n m => rv (MvPolynomial.eval (vfAt z) (p i)))
      (T.extendBase_inverse hGS b)).trans (hh.trans
        (congrArg (fun z : Point (M := M) n m => rv (MvPolynomial.eval (vfAt z) (p i)))
          (T.extendBase_inverse hGS c)).symm)
  have hMember (b c : extendBase C hGS) (he : SameRV b.val c.val) :
      (W.inverseMap b).val ∈ carrier A ↔ (W.inverseMap c).val ∈ carrier A := by
    have hlabel := ((sameRV_iff _ _).mp (W.inverse_contractible b c he)).2
    have hP : ∀ i, rv (MvPolynomial.eval (vfAt (W.inverseMap b).val) (pA i)) =
        rv (MvPolynomial.eval (vfAt (W.inverseMap c).val) (pA i)) := by
      intro i
      simpa only [p,Fin.append_left] using hPoly b c he (Fin.castAdd dR i)
    exact hcontrolA _ _ hlabel hP (Fin.elim0,Fin.elim0)
  have hRelation (b c : extendBase C hGS) (he : SameRV b.val c.val) :
      ∀ z, r (W.inverseMap b).val z ↔ r (W.inverseMap c).val z := by
    have hlabel := ((sameRV_iff _ _).mp (W.inverse_contractible b c he)).2
    apply hcontrolR _ _ hlabel
    intro i
    simpa only [p,Fin.append_right] using hPoly b c he (Fin.natAdd dA i)
  obtain ⟨D,U,hUa,hUG,hDC,hImage,hcomm⟩ :=
    W.restrict_gamma_at hΓ hWG A hAE hA previous hWa
  have hInv (b : D) : (W.inverseMap ⟨b.val,hDC b.property⟩).val = (U.inverseMap b).val := by
    have he : W.toMap ⟨(U.inverseMap b).val,hAE (U.inverseMap b).property⟩ =
        (⟨b.val,hDC b.property⟩ : extendBase C hGS) := by
      apply Subtype.ext
      exact (hcomm (U.inverseMap b)).symm.trans (congrArg Subtype.val (U.apply_inverse b))
    rw [← he,W.inverse_apply]
  refine ⟨l,D,U,hUa,hUG,?_,?_⟩
  · apply (isRVPullback_iff _).mpr
    intro b hb c he
    have hc := (isRVPullback_iff _).mp hC b (hDC hb) c he
    have hbA : (W.inverseMap ⟨b,hDC hb⟩).val ∈ carrier A :=
      (hInv ⟨b,hb⟩).symm ▸ (U.inverseMap ⟨b,hb⟩).property
    have hcA := (hMember ⟨b,hDC hb⟩ ⟨c,hc⟩ he).mp hbA
    rw [hImage]
    refine ⟨⟨(W.inverseMap ⟨c,hc⟩).val,hcA⟩,?_⟩
    have hu : (⟨(W.inverseMap ⟨c,hc⟩).val,hAE hcA⟩ : extendBase E hGS) =
        W.inverseMap ⟨c,hc⟩ := Subtype.ext rfl
    rw [hu,W.apply_inverse]
  · intro b c he z
    have hh := hRelation ⟨b.val,hDC b.property⟩ ⟨c.val,hDC c.property⟩ he z
    rwa [hInv b,hInv c] at hh

/-- All earlier logic, polynomial support and obstacle premises are
constructed from the paper's actual base and genuine saturation. -/
theorem prepare {κ : Cardinal} (hs : SpecialTransformations.Section3.Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00)
    (G : SpecialTransformations.Section3.GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : SpecialTransformations.Section3.GammaParameters.VFGammaGeneratedBase G)
    (hGS : G.real ⊆ S) (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable G (carrier A))
    (r : Point (M := M) n m → Point (M := M) 0 k → Prop)
    (hr : GammaGraphDefinable G r) (previous : Option Bool)
    (hTags : previous = some false → AllTagged A) :
    ∃ l : ℕ, ∃ D : DefSet (M := M) S n l, ∃ U : SpecialBijection A D,
      U.chain.Alternating previous ∧ GammaChainDefinable G U.chain ∧
        IsRVPullback (carrier D) ∧ ∀ b c : D, SameRV b.val c.val →
          ∀ z, r (U.inverseMap b).val z ↔ r (U.inverseMap c).val z :=
  prepare_with_inputs h00 SpecialTransformations.Section3.Values.presentationValuation
    SpecialTransformations.Section3.Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall _ SpecialTransformations.Section3.Values.presentation_compatible)
    (gammaLogicInput G) (gammaPolynomialSupportInput_of_generatedBase G hGenerated)
    hGS A hA r hr previous hTags

theorem chain_append_definable {a b c : ℕ}
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b} {C : DefSet (M := M) S n c}
    (T : Chain S n A B) (U : Chain S n B C)
    (hT : GammaChainDefinable G T) (hU : GammaChainDefinable G U) :
    GammaChainDefinable G (T.append U) := by
  induction T with
  | nil A => exact hU
  | cons p tail ih => exact ⟨hT.1,ih U hT.2 hU⟩

theorem prepare_after {κ : Cardinal} (hs : SpecialTransformations.Section3.Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00)
    (G : SpecialTransformations.Section3.GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : SpecialTransformations.Section3.GammaParameters.VFGammaGeneratedBase G)
    (hGS : G.real ⊆ S) {a : ℕ} {A₀ : DefSet (M := M) S n a} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable G τ.chain)
    (r : Point (M := M) n a → Point (M := M) 0 k → Prop)
    (hr : GammaGraphDefinable G r) :
    ∃ l : ℕ, ∃ D : DefSet (M := M) S n l, ∃ U : SpecialBijection A D,
      ∃ hAlt : (τ.chain.append U.chain).Alternating none,
        GammaChainDefinable G U.chain ∧ IsRVPullback (carrier D) ∧
          ∀ b c : D, SameRV b.val c.val → ∀ z,
            r ((τ.comp U hAlt).inverseMap b).val z ↔
              r ((τ.comp U hAlt).inverseMap c).val z := by
  let hΓ := gammaLogicInput G
  let R : Point (M := M) n m → Point (M := M) 0 k → Prop :=
    fun p z => ∃ q, pointMapGraph τ.inverseMap p q ∧ r q z
  have hR : GammaGraphDefinable G R :=
    hΓ.comp_graph (gamma_inverse_graph hΓ τ hτ) hr
  have hRiff (b : A) (z : Point (M := M) 0 k) : R b.val z ↔ r (τ.inverseMap b).val z := by
    constructor
    · rintro ⟨q,⟨c,hc,hq⟩,hh⟩
      have he : c = b := Subtype.ext hc
      subst c
      exact hq ▸ hh
    · intro hh
      exact ⟨(τ.inverseMap b).val,⟨b,rfl,rfl⟩,hh⟩
  obtain ⟨l,D,U,hUa,hUG,hD,hC⟩ := prepare hs h00 G hsmall hGenerated hGS A
    (GammaChainDefinable.target G τ.chain hτ) R hR (τ.chain.lastKind none)
    (fun h => τ.chain.lastKind_allTagged none (by intro he; cases he) h)
  have hAlt := τ.chain.append_alternating U.chain none τ.alternating hUa
  refine ⟨l,D,U,hAlt,hUG,hD,?_⟩
  intro b c he z
  have hh := hC b c he z
  rw [hRiff,hRiff] at hh
  simpa only [SpecialBijection.comp_inverseMap] using hh

end IntegrationInACVF.Section4.GammaRelationPreparation
