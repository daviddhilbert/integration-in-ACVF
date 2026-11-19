import Integration7.HKPureVFGammaLoci
import Integration7.GammaFunFamilies
import IntegrationSection6.GammaFormulaVFFamilies
import Integration7.MixedVFBaseJacobianDensities
import Integration7.GammaNamedJacobianTransport

/-! Gamma definability of points determined by Gamma relations: VF points are Gamma
singletons over their row base, fibres of Gamma graphs over a VF point are Gamma over the
row base, and coordinates of Gamma singletons lie in the definable closure. Jacobian value
densities of two value maps agree wherever the values agree, in particular at generic
points of mixed base maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput gammaPointSort gammaPointCode)
open SpecialTransformations.Section4 (vfValues)
open SpecialTransformations.Section9 (HasMixedVFJacobianAt)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G B : Base (M := M)} {p u w : ℕ}

/-- A VF point is a Gamma singleton over its row base. -/
theorem gamma_vf_point_singleton (G : Base (M := M)) (y : Fin p → VFType (M := M)) :
    GammaSetDefinable (rowGammaBase G y) {q : Point (M := M) p 0 | q.1 = y} := by
  let B := rowGammaBase G y
  have h := tuple_singleton_definable_base B (fun _ : Fin p => SortTag.vf) (fun j => (y j).val)
    (fun j => real_definableAtBase B .vf _ (definableClosureAt_of_mem (Or.inr ⟨j,rfl⟩) (y j).property))
  have h2 := HK.gamma_pure_vf_locus h
  convert h2 using 1
  ext q
  constructor
  · intro hq
    change vfValues q.1 = fun j => (y j).val
    rw [hq]
    rfl
  · intro hq
    exact SpecialTransformations.Section4.vfValues_injective hq

/-- The fibre of a Gamma graph over a VF point is Gamma over the row base. -/
theorem gamma_graph_vf_fibre {r : Point (M := M) p 0 → Point (M := M) u w → Prop}
    (hr : GammaGraphDefinable G r) (y : Fin p → VFType (M := M)) :
    GammaSetDefinable (rowGammaBase G y) {q | r (y,Fin.elim0) q} := by
  let B := rowGammaBase G y
  let L := gammaLogicInput B
  have hr' : GammaGraphDefinable B r := DefinableOverBase.mono hr Set.subset_union_left (Set.Subset.refl _)
  have h := L.image_graph (L.restrict_graph (gamma_vf_point_singleton G y) hr')
  convert h using 1
  ext q
  constructor
  · intro hq
    exact ⟨(y,Fin.elim0),rfl,hq⟩
  · rintro ⟨p',hp',hq⟩
    have he : p' = (y,Fin.elim0) := Prod.ext hp' (funext fun i => i.elim0)
    rw [he] at hq
    exact hq

/-- Coordinates of a Gamma VF singleton lie in the definable closure. -/
theorem definableClosure_of_gamma_vf_point {x : Fin p → VFType (M := M)}
    (h : GammaSetDefinable B {q : Point (M := M) p 0 | q.1 = x}) (i : Fin p) :
    DefinableClosureAtBase B .vf (x i).val := by
  have hi := (gammaLogicInput B).image_real
    (mixedCoordinatePointMap (fun _ : Fin 1 => i) (Fin.elim0 : Fin 0 → Fin 0) B.real) h
  unfold GammaSetDefinable at hi
  rw [gammaPointSort_vf_zero] at hi
  change DefinableOverBase B (fun _ : Fin 1 => SortTag.vf) {z | z 0 ∈ ({(x i).val} : Set M)}
  convert hi using 1
  ext z
  constructor
  · intro hz
    refine ⟨((fun _ => x i),Fin.elim0),⟨⟨(x,Fin.elim0),Set.mem_univ _⟩,rfl,?_⟩,?_⟩
    · exact Prod.ext rfl (funext fun j => j.elim0)
    · rw [gammaPointCode_vf_zero]
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      exact (Set.mem_singleton_iff.mp hz).symm
  · rintro ⟨q,⟨a,ha,hq⟩,rfl⟩
    rw [gammaPointCode_vf_zero]
    change (q.1 0).val = (x i).val
    rw [← hq]
    change (a.val.1 i).val = (x i).val
    rw [show a.val.1 = x from ha]

theorem gammaPointSort_zero_one : gammaPointSort 0 1 = (fun _ => SortTag.rv) := by
  funext j
  obtain ⟨j,hj⟩ := j
  obtain rfl : j = 0 := by omega
  rfl

theorem gammaPointCode_zero_one (z : Point (M := M) 0 1) : gammaPointCode z = (fun _ => (z.2 0).val) := by
  funext j
  obtain ⟨j,hj⟩ := j
  obtain rfl : j = 0 := by omega
  rfl

/-- An RV value forming a Gamma singleton lies in the definable closure. -/
theorem definableClosure_of_gamma_rv_point {c : CanonicalRV.RVSort M}
    (h : GammaSetDefinable B {q : Point (M := M) 0 1 | q.2 0 = c}) :
    DefinableClosureAtBase B .rv c.val := by
  unfold GammaSetDefinable at h
  rw [gammaPointSort_zero_one] at h
  change DefinableOverBase B (fun _ : Fin 1 => SortTag.rv) {z | z 0 ∈ ({c.val} : Set M)}
  convert h using 1
  ext z
  constructor
  · intro hz
    refine ⟨(Fin.elim0,fun _ => c),rfl,?_⟩
    rw [gammaPointCode_zero_one]
    funext j
    obtain ⟨j,hj⟩ := j
    obtain rfl : j = 0 := by omega
    exact (Set.mem_singleton_iff.mp hz).symm
  · rintro ⟨q,hq,rfl⟩
    rw [gammaPointCode_zero_one]
    change (q.2 0).val = c.val
    rw [show q.2 0 = c from hq]

/-- Jacobian value densities agree where the two value maps agree. -/
theorem jacobian_value_density_eq_of_value {n a : ℕ} {S : Set M}
    {A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) S}
    (j₁ j₂ : SpecialTransformations.DefinableGeometry.Map A
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) S))
    (q : A) (h : (j₁ q).val 0 = (j₂ q).val 0) :
    (jacobianValueDensityForm j₁).value q = (jacobianValueDensityForm j₂).value q := by
  have he : j₁ q = j₂ q := Subtype.ext (funext fun i => by
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact h)
  change (nonzeroRVScalarMap S ((scalarEncodedRVMap S) (j₁ q))).val 0 =
    (nonzeroRVScalarMap S ((scalarEncodedRVMap S) (j₂ q))).val 0
  rw [he]

/-- At generic points, Jacobian values of a mixed base map and of its pure base map agree. -/
theorem jacobian_values_agree_at_generic {n a : ℕ} (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hn : 0 < n)
    {X Y : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawVFSpace (M := M) n) (C.base : Set M)}
    (φ : SpecialTransformations.DefinableGeometry.Map X Y)
    (U : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) (C.base : Set M))
    (hU : ∀ p : U, p.val.1 ∈ X.carrier)
    (jU : SpecialTransformations.DefinableGeometry.Map U
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) (C.base : Set M)))
    (hjU : IsJacobianValueMap (mixedVFBaseMap φ U hU).toImage jU)
    (jX : SpecialTransformations.DefinableGeometry.Map
      (X.prod (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawRVSpace (M := M) 0) (C.base : Set M)))
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) (C.base : Set M)))
    (hjX : IsJacobianValueMap (pureVFMixedMap φ) jX)
    (p : U) (hp : AlgebraicIndependent (vfParameterField (C.base : Set M)) p.val.1) :
    (jU p).val 0 = (jX (pureVFEmptyGraphMap X ⟨p.val.1,hU p⟩)).val 0 := by
  let f := (mixedVFBaseMap φ U hU).toImage
  let q := pureVFEmptyGraphMap X ⟨p.val.1,hU p⟩
  have hq : AlgebraicIndependent (vfParameterField (C.base : Set M)) q.val.1 := hp
  obtain ⟨L,hL⟩ := (mixed_differentiability_almost_everywhere hc C hn f).at_independent hc p hp
  obtain ⟨K,hK⟩ := (mixed_differentiability_almost_everywhere hc C hn (pureVFMixedMap φ)).at_independent hc q hq
  have hLJ : HasMixedVFJacobianAt f p (LinearMap.toMatrix' L).det := by
    obtain ⟨F,hF,hD⟩ := hL
    exact ⟨F,hF,hD.hasJacobianAt⟩
  have hKJ : HasMixedVFJacobianAt (pureVFMixedMap φ) q (LinearMap.toMatrix' K).det := by
    obtain ⟨F,hF,hD⟩ := hK
    exact ⟨F,hF,hD.hasJacobianAt⟩
  have he := mixed_vf_base_jacobian_eq φ U hU p _ _ hKJ hLJ
  rw [hjU p L hL,hjX q K hK]
  exact he.symm

end IntegrationInACVF.Section7
