import Integration7.GammaNamedZeroVFClasses
import Integration7.GammaRawMixedRelations
import Integration7.GammaRVCommonNames
import Integration7.OrdinaryFiniteLiftSurjectivity
import Integration7.SelectedVolumeFamilyZeroProducts
import Integration7.GeneratedBaseStandardContractions
import Section5.GammaSurjectivity
import Section5.GammaLiftRelation
import Integration7.RVCoordinateSelection

/-! Every Gamma-named degree-zero VF volume object is Gamma-isomorphic to the
lift of a Gamma-named degree-zero RV volume object (over a code set
containing the common names). Uses the predecessor's Gamma Corollary 5.7
(finite form). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput GammaIso
  GammaHasVFDimLE)

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)}

theorem zero_vf_set_finite (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : ZeroVFVolumeObject (M := M) (C.base : Set M)) :
    (A.underlying.obj.obj.set.carrier).Finite := by
  obtain ⟨U₀, ⟨e₀⟩⟩ := ordinary_finite_lift_presentation_exists hc C A.underlying
  haveI := (ordinary_zero_volume_domain_finite U₀).to_subtype
  let φ : A.underlying.obj.obj.set → U₀.obj.domain := fun x => liftLabelMap U₀.obj (finiteZeroVFMap e₀ x)
  have hφ : Function.Injective φ := by
    intro x y h
    have h₁ := (zero_lift_label_map_bijective U₀.obj).1 h
    have h₂ := congrArg (finiteZeroVFMap e₀.symm) h₁
    rwa [finiteZeroVFMap_symm_apply, finiteZeroVFMap_symm_apply] at h₂
  haveI := Finite.of_injective φ hφ
  exact Set.toFinite _

theorem zero_vf_gamma_dim (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : ZeroVFVolumeObject (M := M) (C.base : Set M)) (hA : A.Gamma G) :
    GammaHasVFDimLE G (A.underlying.obj.obj.set.carrier :
      Set (Point (M := M) A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2)) 0 := by
  have hfin := zero_vf_set_finite hc C A
  haveI := hfin.to_subtype
  refine ⟨0, le_rfl, 0, 0, fun _ => ((Fin.elim0, Fin.elim0), Fin.elim0), fun _ => Set.toFinite _, ?_⟩
  show GammaGraphDefinable G (fun x (y : Point (M := M) 0 (0 + 0)) =>
    ∃ a : (A.underlying.obj.obj.set.carrier :
      Set (Point (M := M) A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2)), a.val = x ∧
      ∃ t : Fin 0 → Code (M := M), values t = Fin.elim0 ∧
        y = ((Fin.elim0 : Fin 0 → SpecialTransformations.Section5.VF (M := M)),
          Fin.append (Fin.elim0 : Fin 0 → SpecialTransformations.Section5.RV (M := M)) (fun i => (t i).val)))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput G).restrict_graph hA.set (GammaLift.gamma_true_graph (B := G)))
  intro x y
  constructor
  · rintro ⟨hx, -⟩
    refine ⟨⟨x, hx⟩, rfl, Fin.elim0, funext (fun i => Fin.elim0 i), ?_⟩
    exact Prod.ext (funext (fun i => Fin.elim0 i)) (funext (fun i => Fin.elim0 (by simpa using i)))
  · rintro ⟨a, rfl, -⟩
    exact ⟨a.property, trivial⟩

theorem gamma_zero_lift_presentation (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase G)
    (A : ZeroVFVolumeObject (M := M) (C.base : Set M)) (hA : A.Gamma G) :
    ∃ U : ZeroRVVolumeObject (M := M) (C.base : Set M), U.Gamma G ∧
      ∃ e : ZeroVFVolumeIso A (zeroLift U), e.GammaDefinable G := by
  let S := (C.base : Set M)
  let X := A.underlying.obj.obj.set
  have hsmall : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  obtain ⟨W, ⟨e⟩⟩ := SpecialTransformations.Section5.Paper.corollary_5_7_finite_gamma C.uncountable.le
    C.saturated C.model00 G hsmall (generatedBaseVFField hGenerated)
    (X.carrier : Set (Point (M := M) A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2))
    hA.set (zero_vf_gamma_dim hc C A hA) (fun x => A.underlying.property x)
  let W' := W.toGammaRVObject
  let a' := SpecialTransformations.Section5.rvObjectArity W'.object
  let D : Set (Fin a' → CanonicalRV.RVSort M) :=
    {t | ((Fin.elim0, t) : Point (M := M) 0 a') ∈ W'.lift}
  have hpt (p : Point (M := M) 0 a') : ((Fin.elim0, p.2) : Point (M := M) 0 a') = p :=
    Prod.ext (funext (fun i => Fin.elim0 i)) rfl
  have hDl : {p : Point (M := M) 0 a' | p.2 ∈ D} = W'.lift := by
    ext p
    change ((Fin.elim0, p.2) : Point (M := M) 0 a') ∈ W'.lift ↔ p ∈ W'.lift
    rw [hpt]
  have hD : GammaSetDefinable G {p : Point (M := M) 0 a' | p.2 ∈ D} := hDl ▸ W'.lift_definable
  have hDrel := gamma_raw_rv_relation_common_names hc hNames
    ((gammaLogicInput G).restrict_graph hD (GammaLift.gamma_true_graph (B := G) (c := 0) (d := 0)))
  let DS : DefSet (rawRVSpace (M := M) a') S := by
    refine ⟨D, ?_⟩
    convert hDrel.exists_right (rawRVSpace (M := M) a') (rawRVSpace (M := M) 0) using 1
    ext x
    constructor
    · intro hx
      exact ⟨Fin.elim0, hx, trivial⟩
    · rintro ⟨y, hx, -⟩
      exact hx
  haveI : Finite X := (zero_vf_set_finite hc C A).to_subtype
  have hWfin : Finite W'.lift := Finite.of_equiv _ e.equiv
  have hDfin : D.Finite := by
    have h := (Set.toFinite W'.lift).image (fun p : Point (M := M) 0 a' => p.2)
    apply h.subset
    intro t ht
    exact ⟨_, ht, rfl⟩
  let Z₀ : RVObject (M := M) S 0 :=
    ⟨a', DS, (rvCoordinateSelectMap S (Fin.elim0 : Fin 0 → Fin a')).comp (Map.id DS).toUniv⟩
  haveI : Finite DS := hDfin.to_subtype
  let Z₁ : RVFiniteObject (M := M) S 0 := ⟨Z₀, fun _ => Set.toFinite _⟩
  have hlift : W'.lift = ((rvLift Z₀).carrier : Set (Point (M := M) 0 a')) := by
    rw [← hDl]
    ext p
    constructor
    · intro hp
      exact ⟨⟨p.2, hp⟩, rfl, funext (fun i => Fin.elim0 i)⟩
    · rintro ⟨u, hu, -⟩
      change p.2 ∈ D
      rw [← hu]
      exact u.property
  let e' := e.congr rfl hlift
  let g : Map X (rvLift Z₀) := by
    refine ⟨fun x => ⟨(e'.equiv ⟨x.val, x.property⟩).val, (e'.equiv ⟨x.val, x.property⟩).property⟩, ?_⟩
    exact gamma_raw_mixed_relation_common_names hc hNames e'.graph
  have hg : Function.Bijective g := by
    constructor
    · intro x y h
      have h' : e'.equiv ⟨x.val, x.property⟩ = e'.equiv ⟨y.val, y.property⟩ :=
        Subtype.ext (congrArg Subtype.val h)
      exact Subtype.ext (congrArg Subtype.val (e'.equiv.injective h'))
    · intro q
      obtain ⟨x, hx⟩ := e'.equiv.surjective ⟨q.val, q.property⟩
      exact ⟨⟨x.val, x.property⟩, Subtype.ext (congrArg Subtype.val hx)⟩
  let iso : A.underlying ≅ rvLiftFiniteObject (rawRVSpace (M := M) 1) Z₁ := by
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact DefinableSetCat.isoOfBijective g hg
  let labelInv := (liftLabelMap Z₀).inverse (zero_lift_label_map_bijective Z₀)
  let ρ : VolumeForm Z₁.obj.domain := A.form.pullback ((g.inverse hg).comp labelInv)
  let U : ZeroRVVolumeObject (M := M) S := ⟨Z₁, ρ⟩
  have hiso (a : X) : finiteZeroVFMap iso a = g a := rfl
  have hdens : ∀ a, A.form.value a = (zeroLift U).form.value (finiteZeroVFMap iso a) := by
    intro a
    change A.form.value a = A.form.value ((g.inverse hg) (labelInv (liftLabelMap Z₀ (finiteZeroVFMap iso a))))
    rw [Map.inverse_apply, hiso, Map.inverse_apply]
  refine ⟨U, ⟨hD, ?_⟩, ⟨iso, hdens⟩, ?_⟩
  · -- the density of `U` has a Gamma graph
    have L := gammaLogicInput G
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr
      (L.comp_graph (L.swap_graph e'.graph) hA.density)
    intro p y
    constructor
    · rintro ⟨x, ⟨x', rfl, hx'⟩, a, ha, hy⟩
      have ha' : a = ⟨x'.val, x'.property⟩ := Subtype.ext ha
      rw [ha'] at hy
      have hpD : p.2 ∈ D := by
        have := (e'.equiv x').property
        rw [hx'] at this
        exact (hlift ▸ this : p ∈ W'.lift) |> fun h => by rw [← hpt p] at h; exact h
      refine ⟨⟨p.2, hpD⟩, rfl, ?_⟩
      have hlab : labelInv ⟨p.2, hpD⟩ = ⟨p, by rw [← hx']; exact (e'.equiv x').property⟩ := by
        apply (zero_lift_label_map_bijective Z₀).1
        rw [Map.apply_inverse]
        rfl
      have hgx : (g.inverse hg) ⟨p, by rw [← hx']; exact (e'.equiv x').property⟩ = ⟨x'.val, x'.property⟩ := by
        apply hg.1
        rw [Map.apply_inverse]
        exact Subtype.ext hx'.symm
      change (A.form.map ((g.inverse hg) (labelInv ⟨p.2, hpD⟩))).val = y.2
      rw [hlab, hgx]
      exact hy
    · rintro ⟨u, hu, hy⟩
      let q := labelInv u
      let x := (g.inverse hg) q
      have hgq : g x = q := Map.apply_inverse g hg q
      have hqp : q.val = p := by
        have h1 : (liftLabelMap Z₀ q).val = u.val := congrArg Subtype.val (Map.apply_inverse _ _ u)
        refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
        exact h1.trans hu
      refine ⟨x.val, ⟨⟨x.val, x.property⟩, rfl, ?_⟩, x, rfl, hy⟩
      exact (congrArg Subtype.val hgq).trans hqp
  · -- the isomorphism has a Gamma graph
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr e'.graph
    intro p q
    constructor
    · rintro ⟨x, rfl, rfl⟩
      exact ⟨⟨x.val, x.property⟩, rfl, rfl⟩
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨⟨a.val, a.property⟩, rfl, rfl⟩

end IntegrationInACVF.Section7.HK

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)}

/-- The Gamma degree-zero lift on classes. -/
def gammaZeroLiftOnClasses (G : Base (M := M)) (S : Set M) :
    GammaZeroRVClasses G S → GammaZeroVFClasses G S :=
  Quotient.lift (fun U => Quotient.mk (gammaZeroVFSetoid G S) ⟨zeroLift U.val, zeroLift_gamma U.property⟩)
    (fun _ _ ⟨e, he⟩ => Quotient.sound ⟨zeroLiftIso e, zeroLiftIso_gamma e he⟩)

/-- **Gamma-named degree-zero Proposition 7.9.** -/
theorem gamma_zero_lift_on_classes_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase G) :
    Function.Bijective (gammaZeroLiftOnClasses G (C.base : Set M)) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h U =>
      induction b using Quotient.inductionOn with
      | h V =>
        intro he
        obtain ⟨e, hΓ⟩ := Quotient.exact he
        exact Quotient.sound ⟨zeroRVOfLiftIso e, zeroRVOfLiftIso_gamma e hΓ⟩
  · intro a
    induction a using Quotient.inductionOn with
    | h A =>
      obtain ⟨U, hU, e, he⟩ := gamma_zero_lift_presentation hc C hGC hNames hGenerated A.val A.property
      exact ⟨Quotient.mk _ ⟨U, hU⟩, Quotient.sound ⟨e.symm, he.symm⟩⟩

end IntegrationInACVF.Section7.HK
