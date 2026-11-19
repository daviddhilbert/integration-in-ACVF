import Integration7.GammaNamedRVProductObjects
import Integration7.GammaEssentialVolumeGraphs

/-! Gamma-definability of the actual relabelling isomorphisms of corrected
all-degree RV volume objects, and the unit, associativity and zero laws of
actual products on Gamma-named RV classes, at the level of representatives.
Every structural isomorphism is the existing relabelling by an explicit
coordinate map; its graph is Gamma because the map is a coordinate
selection on a Gamma domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput
  PresentedSet pointSpace carrier setDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {a b : ℕ}

theorem gamma_rv_univ_set (B : Base (M := M)) (a : ℕ) (S : Set M) :
    GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ (DefSet.univ (rawRVSpace (M := M) a) S).carrier} := by
  let P := PresentedSet.univ (pointSpace (M := M) 0 a) B.real
  exact (gammaLogicInput B).real_set (carrier P) (setDefinable P)

/-- A map acting on raw tuples by a coordinate selection, on a Gamma domain, is Gamma. -/
theorem gamma_rv_coordinate_map (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S} {E : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A E) (σ : Fin b → Fin a)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier})
    (hF : ∀ w, (F w).val = w.val ∘ σ) : RVMapGamma F B :=
  gamma_real_rv_map_graph hc B F (rvCoordinateSelectMap B.real σ) hA hF

/-- A map out of an empty domain is Gamma. -/
theorem gamma_rv_map_of_empty {A : DefSet (rawRVSpace (M := M) a) S} {E : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A E) (hA : A.carrier = ∅) : RVMapGamma F B := by
  apply GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph (B := B) _ _)
  intro p q
  constructor
  · exact False.elim
  · rintro ⟨u,_,_⟩
    exact (hA.le u.property).elim

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M}

/-- Gamma-definability of an all-degree RV volume isomorphism. -/
def IsoGamma : (n : ℕ) → {U V : RVVolumeObject (M := M) S n} →
    rvVolumeIsoInDegree S n U V → Base (M := M) → Prop
  | 0, _, _, e, B => ZeroRVVolumeIso.GammaDefinable e B
  | _+1, _, _, e, B => RVVolumeIso.GammaDefinable e B

theorem dataRelabelIso_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (D E : RVVolumeData (M := M) (C.base : Set M) n)
    (F : Map D.underlying.obj.domain E.underlying.obj.domain) (hF : Function.Bijective F)
    (hcoord : ∀ u, E.underlying.obj.value (F u) = D.underlying.obj.value u)
    (hφ : ∀ u, E.form.value (F u) = D.form.value u)
    (hD : RVVolumeObject.Gamma n (ofData D) B) (hFΓ : RVMapGamma F B) :
    IsoGamma n (dataRelabelIso hc C D E F hF hcoord hφ) B := by
  cases n with
  | zero => exact hFΓ.congr (fun _ => rfl)
  | succ k =>
    exact gamma_volume_iso_of_preserving_coordinates_full hc C _ hcoord hφ
      (gamma_essential_volume_domain _ hD.coordinates) (hFΓ.congr (fun _ => rfl))

theorem RVVolumeObject.Gamma.unit (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    RVVolumeObject.Gamma 0 (unit S) B :=
  ⟨gamma_rv_univ_set B 0 S,RVMapGamma.of_arity_zero _ (gamma_rv_univ_set B 0 S),
    RVMapGamma.scalarOne hc _ (gamma_rv_univ_set B 0 S)⟩

theorem RVVolumeObject.Gamma.empty (n : ℕ) (S : Set M) :
    RVVolumeObject.Gamma n (HK.empty S n) B := by
  have hE : (underlying S n (HK.empty (M := M) S n)).obj.domain.carrier = ∅ := empty_domain n
  refine ⟨?_,gamma_rv_map_of_empty _ hE,gamma_rv_map_of_empty _ hE⟩
  have h := FiniteRV.gamma_empty_set (B := B) (underlying S n (HK.empty (M := M) S n)).obj.arity
  convert h using 1
  ext p
  change p.2 ∈ (underlying S n (HK.empty (M := M) S n)).obj.domain.carrier ↔ False
  rw [hE]
  exact Iff.rfl

theorem RVVolumeObject.Gamma.dataOfObject {n : ℕ} {U : RVVolumeObject (M := M) S n}
    (hU : RVVolumeObject.Gamma n U B) : RVVolumeObject.Gamma n (ofData (dataOfObject n U)) B := by
  rw [dataOfObject_ofData]
  exact hU

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The Gamma-named class of a uniformly Gamma all-degree object. -/
def gammaNamedRVClass : {n : ℕ} → GammaRVObjects 𝔅 𝔖 n → GammaNamedRVClasses hc C Ξ hΞ n
  | 0, U => Quotient.mk _ ⟨U.val,(RVVolumeObject.Gamma.zero_iff U.val).mp U.property⟩
  | _+1, U => gammaVolumeBlowupClass hc 𝔇 𝔅 ⟨U.val,(RVVolumeObject.Gamma.positive_iff U.val).mp U.property⟩

theorem gammaNamedRVClass_surjective (n : ℕ) :
    Function.Surjective (gammaNamedRVClass hc C Ξ hΞ (n := n)) := by
  cases n with
  | zero =>
    intro a
    induction a using Quotient.inductionOn with
    | h U => exact ⟨⟨U.val,(RVVolumeObject.Gamma.zero_iff U.val).mpr U.property⟩,rfl⟩
  | succ k =>
    intro a
    induction a using Quotient.inductionOn with
    | h U => exact ⟨⟨U.val,(RVVolumeObject.Gamma.positive_iff U.val).mpr U.property⟩,rfl⟩

theorem gammaNamedRVClass_eq_of_iso {n : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n)
    (e : rvVolumeIsoInDegree 𝔖 n U.val V.val) (he : IsoGamma n e 𝔅) :
    gammaNamedRVClass hc C Ξ hΞ U = gammaNamedRVClass hc C Ξ hΞ V := by
  cases n with
  | zero => exact Quotient.sound ⟨e,he⟩
  | succ k => exact gammaVolumeBlowupClass_iso hc 𝔇 𝔅 e he

theorem gammaNamedRVClass_congr {n : ℕ} {U V : GammaRVObjects 𝔅 𝔖 n} (h : U.val = V.val) :
    gammaNamedRVClass hc C Ξ hΞ U = gammaNamedRVClass hc C Ξ hΞ V :=
  congrArg _ (Subtype.ext h)

def gammaUnit : GammaRVObjects 𝔅 𝔖 0 := ⟨unit 𝔖,RVVolumeObject.Gamma.unit hc 𝔖⟩

def gammaEmpty (n : ℕ) : GammaRVObjects 𝔅 𝔖 n := ⟨HK.empty 𝔖 n,RVVolumeObject.Gamma.empty n 𝔖⟩

theorem rv_product_assoc_raw {k l j : ℕ} (A : RVObject (M := M) 𝔖 k) (V : RVObject (M := M) 𝔖 l)
    (W : RVObject (M := M) 𝔖 j) (x : (rvProductObject (rvProductObject A V) W).domain) :
    (rvProductAssocMap A V W x).val = x.val ∘ Fin.cast (Nat.add_assoc A.arity V.arity W.arity).symm := by
  obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (rvProductObject A V).domain W.domain x
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.domain V.domain uv
  rw [rvProductAssocMap_pair]
  change Fin.append u.val (Fin.append v.val w.val) = Fin.append (Fin.append u.val v.val) w.val ∘ _
  rw [Fin.append_assoc]
  funext i
  simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]

/-! ### Laws for any Gamma-isomorphism-invariant class map -/

section Generic
variable {X : ℕ → Type}
  (φ : ∀ {n : ℕ}, GammaRVObjects (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M) n → X n)
variable (hφ : ∀ {n : ℕ} (U V : GammaRVObjects (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M) n)
  (e : rvVolumeIsoInDegree ((gammaNamedCodeContext C Ξ hΞ).base : Set M) n U.val V.val),
  IsoGamma n e (gammaNamedBase C Ξ) → φ U = φ V)
include hc hφ

theorem gen_congr {n : ℕ} {U V : GammaRVObjects 𝔅 𝔖 n} (h : U.val = V.val) : φ U = φ V :=
  congrArg _ (Subtype.ext h)

/-- Relabelling along a Gamma coordinate bijection, with a degree identification. -/
theorem gen_heq_of_reindex {n m : ℕ} (h : n = m)
    (D : RVVolumeData (M := M) 𝔖 n) (E : RVVolumeData (M := M) 𝔖 m)
    (F : Map D.underlying.obj.domain E.underlying.obj.domain) (hF : Function.Bijective F)
    (hcoord : ∀ u, E.underlying.obj.value (F u) ∘ finCongr h = D.underlying.obj.value u)
    (hdens : ∀ u, E.form.value (F u) = D.form.value u)
    (hD : RVVolumeObject.Gamma n (ofData D) 𝔅) (hE : RVVolumeObject.Gamma m (ofData E) 𝔅)
    (hFΓ : RVMapGamma F 𝔅) :
    HEq (φ ⟨ofData D,hD⟩) (φ ⟨ofData E,hE⟩) := by
  subst h
  exact heq_of_eq (hφ _ _
    (dataRelabelIso hc 𝔇 D E F hF hcoord hdens) (dataRelabelIso_gamma hc 𝔇 D E F hF hcoord hdens hD hFΓ))

/-! ### Unit laws -/

theorem gen_product_right_unit {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    φ (U.product hc (gammaUnit hc C Ξ hΞ)) = φ U := by
  let A := underlying 𝔖 n U.val
  let Z := unit (M := M) 𝔖
  let D := productData n 0 U.val Z
  let E := dataOfObject n U.val
  let F := rvProductRightUnitMap A.obj
  have hpair (u : A.obj.domain) (z : Z.underlying.obj.domain) :
      F (rvPackPair A.obj.domain Z.underlying.obj.domain u z) = u := by
    simp only [F,rvProductRightUnitMap,Map.comp_apply]
    exact congrArg (Map.prodFst A.obj.domain Z.underlying.obj.domain)
      (rvUnpack_pair A.obj.domain Z.underlying.obj.domain u z)
  have hD : RVVolumeObject.Gamma n (ofData D) 𝔅 :=
    (U.product hc (gammaUnit hc C Ξ hΞ)).property
  have hFΓ : RVMapGamma F 𝔅 := (gamma_rv_unpack_fst hc A.obj.domain Z.underlying.obj.domain
    (gamma_rv_product_domain_of U.property.domain (RVVolumeObject.Gamma.unit (B := 𝔅) hc 𝔖).domain)).congr
    (fun _ => rfl)
  have h := gen_heq_of_reindex hc C Ξ hΞ φ hφ rfl D E F (rvProductRightUnitMap_bijective A.obj)
    (by
      intro x
      obtain ⟨u,z,rfl⟩ := exists_rvPackPair A.obj.domain Z.underlying.obj.domain x
      change A.obj.value (F (rvPackPair A.obj.domain Z.underlying.obj.domain u z)) =
        (rvProductObject A.obj Z.underlying.obj).value (rvPackPair A.obj.domain Z.underlying.obj.domain u z)
      rw [hpair,rvProductObject_value_pair]
      have hz : Z.underlying.obj.value z = Fin.elim0 := funext (fun i => i.elim0)
      rw [hz]
      simp only [rvAppend,Fin.append_elim0,Fin.cast_refl,Function.comp_id])
    (by
      intro x
      obtain ⟨u,z,rfl⟩ := exists_rvPackPair A.obj.domain Z.underlying.obj.domain x
      exact (congrArg E.form.value (hpair u z)).trans
        ((mul_one (E.form.value u)).symm.trans (productData_density_pair n 0 U.val Z u z).symm))
    hD U.property.dataOfObject hFΓ
  exact (eq_of_heq h).trans (gen_congr hc C Ξ hΞ φ hφ (dataOfObject_ofData n U.val))

theorem gen_product_left_unit {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    HEq (φ ((gammaUnit hc C Ξ hΞ).product hc U)) (φ U) := by
  let A := underlying 𝔖 n U.val
  let Z := unit (M := M) 𝔖
  let D := productData 0 n Z U.val
  let E := dataOfObject n U.val
  let F := (rvProductRightUnitMap A.obj).comp (rvProductSwapMap Z.underlying.obj A.obj)
  have hF : Function.Bijective F :=
    (rvProductRightUnitMap_bijective A.obj).comp (rvProductSwapMap_bijective Z.underlying.obj A.obj)
  have hpair (z : Z.underlying.obj.domain) (u : A.obj.domain) :
      F (rvPackPair Z.underlying.obj.domain A.obj.domain z u) = u := by
    simp only [F,Map.comp_apply,rvProductSwapMap_pair,rvProductRightUnitMap]
    exact congrArg (Map.prodFst A.obj.domain Z.underlying.obj.domain)
      (rvUnpack_pair A.obj.domain Z.underlying.obj.domain u z)
  have hD : RVVolumeObject.Gamma (0+n) (ofData D) 𝔅 := ((gammaUnit hc C Ξ hΞ).product hc U).property
  have hFΓ : RVMapGamma F 𝔅 := by
    have h := gamma_rv_unpack_snd hc Z.underlying.obj.domain A.obj.domain
      (gamma_rv_product_domain_of (RVVolumeObject.Gamma.unit (B := 𝔅) hc 𝔖).domain U.property.domain)
    apply h.congr
    intro x
    obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain A.obj.domain x
    rw [hpair]
    change (Map.prodSnd _ _ (rvUnpack _ _ (rvPackPair _ _ z u))).val = u.val
    rw [rvUnpack_pair]
    rfl
  have h := gen_heq_of_reindex hc C Ξ hΞ φ hφ (Nat.zero_add n) D E F hF
    (by
      intro x
      obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain A.obj.domain x
      change A.obj.value (F (rvPackPair Z.underlying.obj.domain A.obj.domain z u)) ∘ finCongr (Nat.zero_add n) =
        (rvProductObject Z.underlying.obj A.obj).value (rvPackPair Z.underlying.obj.domain A.obj.domain z u)
      rw [hpair,rvProductObject_value_pair]
      have hz : Z.underlying.obj.value z = Fin.elim0 := funext (fun i => i.elim0)
      rw [hz]
      exact (Fin.elim0_append _).symm)
    (by
      intro x
      obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain A.obj.domain x
      exact (congrArg E.form.value (hpair z u)).trans
        ((one_mul (E.form.value u)).symm.trans (productData_density_pair 0 n Z U.val z u).symm))
    hD U.property.dataOfObject hFΓ
  exact h.trans (heq_of_eq (gen_congr hc C Ξ hΞ φ hφ (dataOfObject_ofData n U.val)))


/-! ### Zero laws -/

theorem gen_product_right_zero {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    φ (U.product hc (gammaEmpty C Ξ hΞ m)) =
      φ (gammaEmpty C Ξ hΞ (n+m)) := by
  let D := productData n m U.val (HK.empty 𝔖 m)
  let E := dataOfObject (n+m) (HK.empty 𝔖 (n+m))
  have hD : D.underlying.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let p := rvUnpack (underlying 𝔖 n U.val).obj.domain
      (underlying 𝔖 m (HK.empty 𝔖 m)).obj.domain ⟨x,hx⟩
    exact (empty_domain (S := 𝔖) m).le p.property.2
  have hE : E.underlying.obj.domain.carrier = ∅ := empty_domain (n+m)
  let F := Map.fromEmpty hD E.underlying.obj.domain
  have h := gen_heq_of_reindex hc C Ξ hΞ φ hφ rfl D E F (Map.bijective_of_empty F hD hE)
    (fun x => (hD.le x.property).elim) (fun x => (hD.le x.property).elim)
    (U.product hc (gammaEmpty C Ξ hΞ m)).property (gammaEmpty C Ξ hΞ (n+m)).property.dataOfObject
    (gamma_rv_map_of_empty F hD)
  exact (eq_of_heq h).trans (gen_congr hc C Ξ hΞ φ hφ (dataOfObject_ofData (n+m) _))

theorem gen_product_left_zero {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 m) :
    φ ((gammaEmpty C Ξ hΞ n).product hc U) =
      φ (gammaEmpty C Ξ hΞ (n+m)) := by
  let D := productData n m (HK.empty 𝔖 n) U.val
  let E := dataOfObject (n+m) (HK.empty 𝔖 (n+m))
  have hD : D.underlying.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let p := rvUnpack (underlying 𝔖 n (HK.empty 𝔖 n)).obj.domain
      (underlying 𝔖 m U.val).obj.domain ⟨x,hx⟩
    exact (empty_domain (S := 𝔖) n).le p.property.1
  have hE : E.underlying.obj.domain.carrier = ∅ := empty_domain (n+m)
  let F := Map.fromEmpty hD E.underlying.obj.domain
  have h := gen_heq_of_reindex hc C Ξ hΞ φ hφ rfl D E F (Map.bijective_of_empty F hD hE)
    (fun x => (hD.le x.property).elim) (fun x => (hD.le x.property).elim)
    ((gammaEmpty C Ξ hΞ n).product hc U).property (gammaEmpty C Ξ hΞ (n+m)).property.dataOfObject
    (gamma_rv_map_of_empty F hD)
  exact (eq_of_heq h).trans (gen_congr hc C Ξ hΞ φ hφ (dataOfObject_ofData (n+m) _))

/-! ### Associativity -/

set_option allowUnsafeReducibility true in
attribute [local reducible] productData rvFiniteProductObject rvProductObject in
theorem gen_product_assoc {n m l : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V : GammaRVObjects 𝔅 𝔖 m)
    (W : GammaRVObjects 𝔅 𝔖 l) :
    HEq (φ ((U.product hc V).product hc W))
      (φ (U.product hc (V.product hc W))) := by
  obtain ⟨U,hU⟩ := U
  obtain ⟨V,hV⟩ := V
  obtain ⟨W,hW⟩ := W
  have hUVW := RVVolumeObject.Gamma.product hc (RVVolumeObject.Gamma.product hc hU hV) hW
  have hUVW' := RVVolumeObject.Gamma.product hc hU (RVVolumeObject.Gamma.product hc hV hW)
  have hdom := gamma_rv_product_domain_of (gamma_rv_product_domain_of hU.domain hV.domain) hW.domain
  change HEq (φ ⟨ofData (productData (n+m) l (HK.product 𝔖 n m U V) W),hUVW⟩)
    (φ ⟨ofData (productData n (m+l) U (HK.product 𝔖 m l V W)),hUVW'⟩)
  revert hUVW hUVW' hdom
  cases n <;> cases m <;> cases l
  all_goals
    intro hUVW hUVW' hdom
    let A := underlying 𝔖 _ U
    let Bv := underlying 𝔖 _ V
    let L := underlying 𝔖 _ W
    exact gen_heq_of_reindex hc C Ξ hΞ φ hφ (Nat.add_assoc _ _ _) _ _
      (rvProductAssocMap A.obj Bv.obj L.obj) (rvProductAssocMap_bijective A.obj Bv.obj L.obj)
      (by
        intro x
        obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (rvProductObject A.obj Bv.obj).domain L.obj.domain x
        obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain Bv.obj.domain uv
        change (rvProductObject A.obj (rvProductObject Bv.obj L.obj)).value
          (rvProductAssocMap A.obj Bv.obj L.obj
            (rvPackPair (rvProductObject A.obj Bv.obj).domain L.obj.domain
              (rvPackPair A.obj.domain Bv.obj.domain u v) w)) ∘ finCongr (Nat.add_assoc _ _ _) =
            (rvProductObject (rvProductObject A.obj Bv.obj) L.obj).value
              (rvPackPair (rvProductObject A.obj Bv.obj).domain L.obj.domain
                (rvPackPair A.obj.domain Bv.obj.domain u v) w)
        rw [rvProductAssocMap_pair,rvProductObject_value_pair,rvProductObject_value_pair,
          rvProductObject_value_pair,rvProductObject_value_pair]
        exact (Fin.append_assoc (A.obj.value u) (Bv.obj.value v) (L.obj.value w)).symm)
      (by
        intro x
        obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (rvProductObject A.obj Bv.obj).domain L.obj.domain x
        obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain Bv.obj.domain uv
        apply (congrArg (productData _ _ U (HK.product 𝔖 _ _ V W)).form.value
          (rvProductAssocMap_pair A.obj Bv.obj L.obj u v w)).trans
        exact (productData_density_pair _ _ U (HK.product 𝔖 _ _ V W) u (rvPackPair Bv.obj.domain L.obj.domain v w)).trans
          ((congrArg (fun t => (form 𝔖 _ U).value u * t) (product_density_pair _ _ V W v w)).trans
            ((mul_assoc ((form 𝔖 _ U).value u) ((form 𝔖 _ V).value v) ((form 𝔖 _ W).value w)).symm.trans
              ((congrArg (fun t => t * (form 𝔖 _ W).value w) (product_density_pair _ _ U V u v)).symm.trans
                (productData_density_pair _ _ (HK.product 𝔖 _ _ U V) W (rvPackPair A.obj.domain Bv.obj.domain u v) w).symm))))
      hUVW hUVW' (gamma_rv_coordinate_map hc (rvProductAssocMap A.obj Bv.obj L.obj) _ hdom
        (rv_product_assoc_raw C Ξ hΞ A.obj Bv.obj L.obj))


end Generic

/-! ### Laws on Gamma-named blowup classes -/

theorem gammaNamedRVClass_heq_of_reindex {n m : ℕ} (h : n = m)
    (D : RVVolumeData (M := M) 𝔖 n) (E : RVVolumeData (M := M) 𝔖 m)
    (F : Map D.underlying.obj.domain E.underlying.obj.domain) (hF : Function.Bijective F)
    (hcoord : ∀ u, E.underlying.obj.value (F u) ∘ finCongr h = D.underlying.obj.value u)
    (hφ : ∀ u, E.form.value (F u) = D.form.value u)
    (hD : RVVolumeObject.Gamma n (ofData D) 𝔅) (hE : RVVolumeObject.Gamma m (ofData E) 𝔅)
    (hFΓ : RVMapGamma F 𝔅) :
    HEq (gammaNamedRVClass hc C Ξ hΞ ⟨ofData D,hD⟩) (gammaNamedRVClass hc C Ξ hΞ ⟨ofData E,hE⟩) :=
  gen_heq_of_reindex hc C Ξ hΞ (X := GammaNamedRVClasses hc C Ξ hΞ) (gammaNamedRVClass hc C Ξ hΞ)
    (gammaNamedRVClass_eq_of_iso hc C Ξ hΞ) h D E F hF hcoord hφ hD hE hFΓ

theorem gamma_product_right_unit {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVClass hc C Ξ hΞ (U.product hc (gammaUnit hc C Ξ hΞ)) = gammaNamedRVClass hc C Ξ hΞ U :=
  gen_product_right_unit hc C Ξ hΞ (X := GammaNamedRVClasses hc C Ξ hΞ) (gammaNamedRVClass hc C Ξ hΞ)
    (gammaNamedRVClass_eq_of_iso hc C Ξ hΞ) U

theorem gamma_product_left_unit {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    HEq (gammaNamedRVClass hc C Ξ hΞ ((gammaUnit hc C Ξ hΞ).product hc U)) (gammaNamedRVClass hc C Ξ hΞ U) :=
  gen_product_left_unit hc C Ξ hΞ (X := GammaNamedRVClasses hc C Ξ hΞ) (gammaNamedRVClass hc C Ξ hΞ)
    (gammaNamedRVClass_eq_of_iso hc C Ξ hΞ) U

theorem gamma_product_right_zero {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVClass hc C Ξ hΞ (U.product hc (gammaEmpty C Ξ hΞ m)) =
      gammaNamedRVClass hc C Ξ hΞ (gammaEmpty C Ξ hΞ (n+m)) :=
  gen_product_right_zero hc C Ξ hΞ (X := GammaNamedRVClasses hc C Ξ hΞ) (gammaNamedRVClass hc C Ξ hΞ)
    (gammaNamedRVClass_eq_of_iso hc C Ξ hΞ) U

theorem gamma_product_left_zero {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVClass hc C Ξ hΞ ((gammaEmpty C Ξ hΞ n).product hc U) =
      gammaNamedRVClass hc C Ξ hΞ (gammaEmpty C Ξ hΞ (n+m)) :=
  gen_product_left_zero hc C Ξ hΞ (X := GammaNamedRVClasses hc C Ξ hΞ) (gammaNamedRVClass hc C Ξ hΞ)
    (gammaNamedRVClass_eq_of_iso hc C Ξ hΞ) U

theorem gamma_product_assoc {n m l : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V : GammaRVObjects 𝔅 𝔖 m)
    (W : GammaRVObjects 𝔅 𝔖 l) :
    HEq (gammaNamedRVClass hc C Ξ hΞ ((U.product hc V).product hc W))
      (gammaNamedRVClass hc C Ξ hΞ (U.product hc (V.product hc W))) :=
  gen_product_assoc hc C Ξ hΞ (X := GammaNamedRVClasses hc C Ξ hΞ) (gammaNamedRVClass hc C Ξ hΞ)
    (gammaNamedRVClass_eq_of_iso hc C Ξ hΞ) U V W

end IntegrationInACVF.Section7.HK
