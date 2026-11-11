import IntegrationSection5.CoordinateInjectivityPartition
import IntegrationSection5.CoordinateContext

/-! The uniform coordinate refinement at any selected source VF coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {p m u w : ℕ}

structure CoordinateRVPartition (G : GammaParameters.Base (M := M))
    {A : Set (Point (M := M) (p+1) m)} {B : Set (Point (M := M) u w)}
    (i : Fin (p+1)) (f : A → B) where
  arity : ℕ
  code : GammaRVMap G A arity
  pieces : Option (Fin u) → Set (Point (M := M) (p+1) m)
  definable : ∀ k, GammaSetDefinable G (pieces k)
  subset : ∀ k, pieces k ⊆ A
  disjoint : ∀ k l, k ≠ l → Disjoint (pieces k) (pieces l)
  cover : ∀ a : A, ∃ k, a.val ∈ pieces k
  coordinate : Option (Fin u) → Fin u
  injective : ∀ k, ∀ a b : A, a.val ∈ pieces k → b.val ∈ pieces k →
    SameCoordinateContext i a.val b.val → code.toFun a = code.toFun b →
      vfAt (f a).val (coordinate k) = vfAt (f b).val (coordinate k) → a = b

theorem coordinate_injective_partition_at {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (A : DefSet (M := M) S (p+1) m) (hA : GammaSetDefinable G (carrier A))
    {B : DefSet (M := M) S u w} (hu : 0 < u) (f : Map A B) (hbij : Function.Bijective f)
    (hf : GammaGraphDefinable G (pointMapGraph f)) (i : Fin (p+1)) :
    Nonempty (CoordinateRVPartition G i f) := by
  let σ := Equiv.swap (0 : Fin (p+1)) i
  let e := vfPermutationBijection A σ
  have he := vfPermutationBijection_bijective A σ
  have heG := gamma_vfPermutation_graph A hA σ
  let e' := Map.inverse e he
  let f' := Map.comp f e'
  have hf' : GammaGraphDefinable G (pointMapGraph f') :=
    gamma_composition_graph e' f (gamma_inverse_map_graph e he heG) hf
  obtain ⟨r,R,P,hP,hsub,hdis,hcover,hinj⟩ := coordinate_injective_rv_partition hκ hs h00 G hsmall δ hδ
    (vfPermutationImage A σ) (gamma_vfPermutationImage A hA σ) hu f' (hbij.comp (Equiv.ofBijective e he).symm.bijective) hf'
  choose j hj using hinj
  let Q := R.precomp e heG
  let D (k : Option (Fin u)) := {a | ∃ b : A, b.val = a ∧ (e b).val ∈ P k}
  have hD (k) : GammaSetDefinable G (D k) := gamma_map_preimage e heG (hP k)
  have hmem (k) (a : A) : a.val ∈ D k ↔ (e a).val ∈ P k := by
    constructor
    · rintro ⟨b,hb,hbP⟩
      exact (Subtype.ext hb : b = a) ▸ hbP
    · intro h
      exact ⟨a,rfl,h⟩
  refine ⟨⟨r,Q,D,hD,?_,?_,?_,j,?_⟩⟩
  · intro k a ha
    obtain ⟨b,hb,_⟩ := ha
    exact hb ▸ b.property
  · intro k l hkl
    apply Set.disjoint_left.mpr
    intro a hak hal
    obtain ⟨b,hb,hbP⟩ := hak
    have hc : b.val ∈ D l := hb.symm ▸ hal
    exact Set.disjoint_left.mp (hdis k l hkl) hbP ((hmem l b).mp hc)
  · intro a
    obtain ⟨k,hk⟩ := hcover (e a)
    exact ⟨k,(hmem k a).mpr hk⟩
  · intro k a b ha hb hctx hcode hscalar
    apply he.1
    apply hj k (e a) (e b) ((hmem k a).mp ha) ((hmem k b).mp hb)
    · apply (sameCoordinateContext_zero_iff _ _).mp
      apply (sameCoordinateContext_permutation σ 0 a.val b.val).mpr
      simpa only [σ,Equiv.swap_apply_left] using hctx
    · exact hcode
    · change vfAt (f (Map.inverse e he (e a))).val (j k) =
        vfAt (f (Map.inverse e he (e b))).val (j k)
      simpa only [Map.inverse_apply] using hscalar

end IntegrationInACVF.Section5
