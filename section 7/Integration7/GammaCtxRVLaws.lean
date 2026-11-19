import Integration7.GammaNamedRVSemiring
import Integration7.GammaNamedRVProductDistributivity

/-! **Gamma RV class laws in an arbitrary context.** The congruence, unit, zero, associativity and
distributivity laws of actual products of Gamma all-degree RV objects, for an arbitrary code
context `C` and Gamma base `B₀`. These are the laws of `GammaNamedRVProductLaws`,
`GammaNamedRVProductDistributivity` and `GammaNamedRVSemiring` with the named context replaced by a
general one (the proofs never used the named context); they apply in particular to the row contexts
of Gamma-named functions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput
  PresentedSet pointSpace carrier setDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK.Ctx
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (B₀ : Base (M := M))

set_option quotPrecheck false
local notation "𝔅" => B₀
local notation "𝔇" => C
local notation "𝔖" => (C.base : Set M)

/-- Gamma RV volume classes in every degree, in the context `C` over the base `B₀`. This is a `def`
(not an `abbrev`) so that its instances never apply to the named classes `HK.GammaNamedRVClasses`. -/
def GammaNamedRVClasses : ℕ → Type
  | 0 => GammaZeroRVClasses B₀ (C.base : Set M)
  | k+1 => GammaVolumeBlowupClasses hc C B₀ k

instance gammaNamedRVClassesAddCommMonoid : (n : ℕ) → AddCommMonoid (GammaNamedRVClasses hc C B₀ n)
  | 0 => gammaZeroRVAddCommMonoid hc
  | k+1 => inferInstanceAs (AddCommMonoid (GammaVolumeBlowupClasses hc C B₀ k))



/-- The Gamma-named class of a uniformly Gamma all-degree object. -/
def gammaNamedRVClass : {n : ℕ} → GammaRVObjects 𝔅 𝔖 n → GammaNamedRVClasses hc C B₀ n
  | 0, U => Quotient.mk _ ⟨U.val,(RVVolumeObject.Gamma.zero_iff U.val).mp U.property⟩
  | _+1, U => gammaVolumeBlowupClass hc 𝔇 𝔅 ⟨U.val,(RVVolumeObject.Gamma.positive_iff U.val).mp U.property⟩

theorem gammaNamedRVClass_surjective (n : ℕ) :
    Function.Surjective (gammaNamedRVClass hc C B₀ (n := n)) := by
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
    gammaNamedRVClass hc C B₀ U = gammaNamedRVClass hc C B₀ V := by
  cases n with
  | zero => exact Quotient.sound ⟨e,he⟩
  | succ k => exact gammaVolumeBlowupClass_iso hc 𝔇 𝔅 e he

theorem gammaNamedRVClass_congr {n : ℕ} {U V : GammaRVObjects 𝔅 𝔖 n} (h : U.val = V.val) :
    gammaNamedRVClass hc C B₀ U = gammaNamedRVClass hc C B₀ V :=
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
  (φ : ∀ {n : ℕ}, GammaRVObjects B₀ (C.base : Set M) n → X n)
variable (hφ : ∀ {n : ℕ} (U V : GammaRVObjects B₀ (C.base : Set M) n)
  (e : rvVolumeIsoInDegree (C.base : Set M) n U.val V.val),
  IsoGamma n e B₀ → φ U = φ V)
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
    φ (U.product hc (gammaUnit hc C B₀)) = φ U := by
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
    (U.product hc (gammaUnit hc C B₀)).property
  have hFΓ : RVMapGamma F 𝔅 := (gamma_rv_unpack_fst hc A.obj.domain Z.underlying.obj.domain
    (gamma_rv_product_domain_of U.property.domain (RVVolumeObject.Gamma.unit (B := 𝔅) hc 𝔖).domain)).congr
    (fun _ => rfl)
  have h := gen_heq_of_reindex hc C B₀ φ hφ rfl D E F (rvProductRightUnitMap_bijective A.obj)
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
  exact (eq_of_heq h).trans (gen_congr hc C B₀ φ hφ (dataOfObject_ofData n U.val))

theorem gen_product_left_unit {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    HEq (φ ((gammaUnit hc C B₀).product hc U)) (φ U) := by
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
  have hD : RVVolumeObject.Gamma (0+n) (ofData D) 𝔅 := ((gammaUnit hc C B₀).product hc U).property
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
  have h := gen_heq_of_reindex hc C B₀ φ hφ (Nat.zero_add n) D E F hF
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
  exact h.trans (heq_of_eq (gen_congr hc C B₀ φ hφ (dataOfObject_ofData n U.val)))


/-! ### Zero laws -/

theorem gen_product_right_zero {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    φ (U.product hc (gammaEmpty C B₀ m)) =
      φ (gammaEmpty C B₀ (n+m)) := by
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
  have h := gen_heq_of_reindex hc C B₀ φ hφ rfl D E F (Map.bijective_of_empty F hD hE)
    (fun x => (hD.le x.property).elim) (fun x => (hD.le x.property).elim)
    (U.product hc (gammaEmpty C B₀ m)).property (gammaEmpty C B₀ (n+m)).property.dataOfObject
    (gamma_rv_map_of_empty F hD)
  exact (eq_of_heq h).trans (gen_congr hc C B₀ φ hφ (dataOfObject_ofData (n+m) _))

theorem gen_product_left_zero {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 m) :
    φ ((gammaEmpty C B₀ n).product hc U) =
      φ (gammaEmpty C B₀ (n+m)) := by
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
  have h := gen_heq_of_reindex hc C B₀ φ hφ rfl D E F (Map.bijective_of_empty F hD hE)
    (fun x => (hD.le x.property).elim) (fun x => (hD.le x.property).elim)
    ((gammaEmpty C B₀ n).product hc U).property (gammaEmpty C B₀ (n+m)).property.dataOfObject
    (gamma_rv_map_of_empty F hD)
  exact (eq_of_heq h).trans (gen_congr hc C B₀ φ hφ (dataOfObject_ofData (n+m) _))

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
    exact gen_heq_of_reindex hc C B₀ φ hφ (Nat.add_assoc _ _ _) _ _
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
        (rv_product_assoc_raw C A.obj Bv.obj L.obj))


end Generic

/-! ### Laws on Gamma-named blowup classes -/

theorem gammaNamedRVClass_heq_of_reindex {n m : ℕ} (h : n = m)
    (D : RVVolumeData (M := M) 𝔖 n) (E : RVVolumeData (M := M) 𝔖 m)
    (F : Map D.underlying.obj.domain E.underlying.obj.domain) (hF : Function.Bijective F)
    (hcoord : ∀ u, E.underlying.obj.value (F u) ∘ finCongr h = D.underlying.obj.value u)
    (hφ : ∀ u, E.form.value (F u) = D.form.value u)
    (hD : RVVolumeObject.Gamma n (ofData D) 𝔅) (hE : RVVolumeObject.Gamma m (ofData E) 𝔅)
    (hFΓ : RVMapGamma F 𝔅) :
    HEq (gammaNamedRVClass hc C B₀ ⟨ofData D,hD⟩) (gammaNamedRVClass hc C B₀ ⟨ofData E,hE⟩) :=
  gen_heq_of_reindex hc C B₀ (X := GammaNamedRVClasses hc C B₀) (gammaNamedRVClass hc C B₀)
    (gammaNamedRVClass_eq_of_iso hc C B₀) h D E F hF hcoord hφ hD hE hFΓ

theorem gamma_product_right_unit {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVClass hc C B₀ (U.product hc (gammaUnit hc C B₀)) = gammaNamedRVClass hc C B₀ U :=
  gen_product_right_unit hc C B₀ (X := GammaNamedRVClasses hc C B₀) (gammaNamedRVClass hc C B₀)
    (gammaNamedRVClass_eq_of_iso hc C B₀) U

theorem gamma_product_left_unit {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    HEq (gammaNamedRVClass hc C B₀ ((gammaUnit hc C B₀).product hc U)) (gammaNamedRVClass hc C B₀ U) :=
  gen_product_left_unit hc C B₀ (X := GammaNamedRVClasses hc C B₀) (gammaNamedRVClass hc C B₀)
    (gammaNamedRVClass_eq_of_iso hc C B₀) U

theorem gamma_product_right_zero {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVClass hc C B₀ (U.product hc (gammaEmpty C B₀ m)) =
      gammaNamedRVClass hc C B₀ (gammaEmpty C B₀ (n+m)) :=
  gen_product_right_zero hc C B₀ (X := GammaNamedRVClasses hc C B₀) (gammaNamedRVClass hc C B₀)
    (gammaNamedRVClass_eq_of_iso hc C B₀) U

theorem gamma_product_left_zero {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVClass hc C B₀ ((gammaEmpty C B₀ n).product hc U) =
      gammaNamedRVClass hc C B₀ (gammaEmpty C B₀ (n+m)) :=
  gen_product_left_zero hc C B₀ (X := GammaNamedRVClasses hc C B₀) (gammaNamedRVClass hc C B₀)
    (gammaNamedRVClass_eq_of_iso hc C B₀) U

theorem gamma_product_assoc {n m l : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V : GammaRVObjects 𝔅 𝔖 m)
    (W : GammaRVObjects 𝔅 𝔖 l) :
    HEq (gammaNamedRVClass hc C B₀ ((U.product hc V).product hc W))
      (gammaNamedRVClass hc C B₀ (U.product hc (V.product hc W))) :=
  gen_product_assoc hc C B₀ (X := GammaNamedRVClasses hc C B₀) (gammaNamedRVClass hc C B₀)
    (gammaNamedRVClass_eq_of_iso hc C B₀) U V W



theorem gammaNamedRVClass_coprod {n : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVClass hc C B₀ (U.coprod V) =
      gammaNamedRVClass hc C B₀ U + gammaNamedRVClass hc C B₀ V := by
  cases n with
  | zero => rfl
  | succ k => rfl

section Generic
variable {X : ℕ → Type}
  (φ : ∀ {n : ℕ}, GammaRVObjects B₀ (C.base : Set M) n → X n)
variable (hφ : ∀ {n : ℕ} (U V : GammaRVObjects B₀ (C.base : Set M) n)
  (e : rvVolumeIsoInDegree (C.base : Set M) n U.val V.val),
  IsoGamma n e B₀ → φ U = φ V)
include hc hφ

set_option allowUnsafeReducibility true in
attribute [local reducible] RVVolumeData.coprod productData rvFiniteProductObject
  rvFiniteCoprodObject rvCoprodObject rvProductObject in
theorem gen_product_right_distrib {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V W : GammaRVObjects 𝔅 𝔖 m) :
    φ (U.product hc (V.coprod W)) =
      φ ((U.product hc V).coprod (U.product hc W)) := by
  obtain ⟨U,hU⟩ := U
  obtain ⟨V,hV⟩ := V
  obtain ⟨W,hW⟩ := W
  let D := productData n m U V
  let E := productData n m U W
  let G := productData n m U (HK.coprod 𝔖 m V W)
  have hF : RVVolumeObject.Gamma (n+m) (ofData (D.coprod E)) 𝔅 := by
    rw [data_coprod_ofData]
    exact (RVVolumeObject.Gamma.product hc hU hV).coprod (RVVolumeObject.Gamma.product hc hU hW)
  have hG : RVVolumeObject.Gamma (n+m) (ofData G) 𝔅 := RVVolumeObject.Gamma.product hc hU (hV.coprod hW)
  have hAd := hU.domain
  have hBd := hV.domain
  have hLd := hW.domain
  have key : φ ⟨ofData (D.coprod E),hF⟩ = φ ⟨ofData G,hG⟩ := by
    revert hF hG hAd hBd hLd
    cases n <;> cases m
    all_goals
      intro hF hG hAd hBd hLd
      let A := underlying 𝔖 _ U
      let Bv := underlying 𝔖 _ V
      let L := underlying 𝔖 _ W
      let ωU := form 𝔖 _ U
      exact eq_of_heq (gen_heq_of_reindex hc C B₀ φ hφ rfl (D.coprod E) G
        (rvProductCoprodFold A.obj Bv.obj L.obj).map (rvProductCoprodFold_bijective A.obj Bv.obj L.obj)
        (by
          intro x
          change (rvProductObject A.obj (rvCoprodObject Bv.obj L.obj)).value _ =
            (rvCoprodObject (rvProductObject A.obj Bv.obj) (rvProductObject A.obj L.obj)).value x
          rcases rvObjectCoprod_cases (rvProductObject A.obj Bv.obj) (rvProductObject A.obj L.obj) x
            with ⟨a,rfl⟩ | ⟨a,rfl⟩
          · obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain Bv.obj.domain a
            rw [rvProductCoprodFold_left,rvProductMap_pair,rvProductObject_value_pair,
              rvCoprod_value_left,rvCoprod_value_left,rvProductObject_value_pair]
            rfl
          · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
            rw [rvProductCoprodFold_right,rvProductMap_pair,rvProductObject_value_pair,
              rvCoprod_value_right,rvCoprod_value_right,rvProductObject_value_pair]
            rfl)
        (by
          intro x
          rcases rvObjectCoprod_cases (rvProductObject A.obj Bv.obj) (rvProductObject A.obj L.obj) x
            with ⟨a,rfl⟩ | ⟨a,rfl⟩
          · obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain Bv.obj.domain a
            have he := (rvProductCoprodFold_left A.obj Bv.obj L.obj (rvPackPair _ _ u v)).trans
              (rvProductMap_pair (Map.id A.obj.domain) (rvCoprodLeftMap Bv.obj L.obj) u v)
            exact (congrArg G.form.value he).trans
              ((productData_density_pair _ _ U (HK.coprod 𝔖 _ V W) u (rvCoprodLeftMap Bv.obj L.obj v)).trans
                ((congrArg (fun t => ωU.value u * t) (coprod_density_left _ V W v)).trans
                  ((productData_density_pair _ _ U V u v).symm.trans
                    (RVVolumeData.coprod_density_left D E (rvPackPair _ _ u v)).symm)))
          · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
            have he := (rvProductCoprodFold_right A.obj Bv.obj L.obj (rvPackPair _ _ u w)).trans
              (rvProductMap_pair (Map.id A.obj.domain) (rvCoprodRightMap Bv.obj L.obj) u w)
            exact (congrArg G.form.value he).trans
              ((productData_density_pair _ _ U (HK.coprod 𝔖 _ V W) u (rvCoprodRightMap Bv.obj L.obj w)).trans
                ((congrArg (fun t => ωU.value u * t) (coprod_density_right _ V W w)).trans
                  ((productData_density_pair _ _ U W u w).symm.trans
                    (RVVolumeData.coprod_density_right D E (rvPackPair _ _ u w)).symm))))
        hF hG (gamma_rv_product_coprod_fold hc A.obj Bv.obj L.obj hAd hBd hLd))
  exact key.symm.trans (gen_congr hc C B₀ φ hφ (data_coprod_ofData D E))

set_option allowUnsafeReducibility true in
attribute [local reducible] RVVolumeData.coprod productData rvFiniteProductObject
  rvFiniteCoprodObject rvCoprodObject rvProductObject in
theorem gen_product_left_distrib {n m : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n) (W : GammaRVObjects 𝔅 𝔖 m) :
    φ ((U.coprod V).product hc W) =
      φ ((U.product hc W).coprod (V.product hc W)) := by
  obtain ⟨U,hU⟩ := U
  obtain ⟨V,hV⟩ := V
  obtain ⟨W,hW⟩ := W
  let D := productData n m U W
  let E := productData n m V W
  let G := productData n m (HK.coprod 𝔖 n U V) W
  have hF : RVVolumeObject.Gamma (n+m) (ofData (D.coprod E)) 𝔅 := by
    rw [data_coprod_ofData]
    exact (RVVolumeObject.Gamma.product hc hU hW).coprod (RVVolumeObject.Gamma.product hc hV hW)
  have hG : RVVolumeObject.Gamma (n+m) (ofData G) 𝔅 := RVVolumeObject.Gamma.product hc (hU.coprod hV) hW
  have hAd := hU.domain
  have hBd := hV.domain
  have hLd := hW.domain
  have key : φ ⟨ofData (D.coprod E),hF⟩ = φ ⟨ofData G,hG⟩ := by
    revert hF hG hAd hBd hLd
    cases n <;> cases m
    all_goals
      intro hF hG hAd hBd hLd
      let A := underlying 𝔖 _ U
      let Bv := underlying 𝔖 _ V
      let L := underlying 𝔖 _ W
      let ωW := form 𝔖 _ W
      exact eq_of_heq (gen_heq_of_reindex hc C B₀ φ hφ rfl (D.coprod E) G
        (rvLeftProductCoprodFold A.obj Bv.obj L.obj).map (rvLeftProductCoprodFold_bijective A.obj Bv.obj L.obj)
        (by
          intro x
          change (rvProductObject (rvCoprodObject A.obj Bv.obj) L.obj).value _ =
            (rvCoprodObject (rvProductObject A.obj L.obj) (rvProductObject Bv.obj L.obj)).value x
          rcases rvObjectCoprod_cases (rvProductObject A.obj L.obj) (rvProductObject Bv.obj L.obj) x
            with ⟨a,rfl⟩ | ⟨a,rfl⟩
          · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
            rw [rvLeftProductCoprodFold_left,rvProductMap_pair,rvProductObject_value_pair,
              rvCoprod_value_left,rvCoprod_value_left,rvProductObject_value_pair]
            rfl
          · obtain ⟨v,w,rfl⟩ := exists_rvPackPair Bv.obj.domain L.obj.domain a
            rw [rvLeftProductCoprodFold_right,rvProductMap_pair,rvProductObject_value_pair,
              rvCoprod_value_right,rvCoprod_value_right,rvProductObject_value_pair]
            rfl)
        (by
          intro x
          rcases rvObjectCoprod_cases (rvProductObject A.obj L.obj) (rvProductObject Bv.obj L.obj) x
            with ⟨a,rfl⟩ | ⟨a,rfl⟩
          · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
            have he := (rvLeftProductCoprodFold_left A.obj Bv.obj L.obj (rvPackPair _ _ u w)).trans
              (rvProductMap_pair (rvCoprodLeftMap A.obj Bv.obj) (Map.id L.obj.domain) u w)
            exact (congrArg G.form.value he).trans
              ((productData_density_pair _ _ (HK.coprod 𝔖 _ U V) W (rvCoprodLeftMap A.obj Bv.obj u) w).trans
                ((congrArg (fun t => t * ωW.value w) (coprod_density_left _ U V u)).trans
                  ((productData_density_pair _ _ U W u w).symm.trans
                    (RVVolumeData.coprod_density_left D E (rvPackPair _ _ u w)).symm)))
          · obtain ⟨v,w,rfl⟩ := exists_rvPackPair Bv.obj.domain L.obj.domain a
            have he := (rvLeftProductCoprodFold_right A.obj Bv.obj L.obj (rvPackPair _ _ v w)).trans
              (rvProductMap_pair (rvCoprodRightMap A.obj Bv.obj) (Map.id L.obj.domain) v w)
            exact (congrArg G.form.value he).trans
              ((productData_density_pair _ _ (HK.coprod 𝔖 _ U V) W (rvCoprodRightMap A.obj Bv.obj v) w).trans
                ((congrArg (fun t => t * ωW.value w) (coprod_density_right _ U V v)).trans
                  ((productData_density_pair _ _ V W v w).symm.trans
                    (RVVolumeData.coprod_density_right D E (rvPackPair _ _ v w)).symm))))
        hF hG (gamma_rv_left_product_coprod_fold hc A.obj Bv.obj L.obj hAd hBd hLd))
  exact key.symm.trans (gen_congr hc C B₀ φ hφ (data_coprod_ofData D E))

end Generic

theorem gamma_product_right_distrib {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V W : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVClass hc C B₀ (U.product hc (V.coprod W)) =
      gammaNamedRVClass hc C B₀ ((U.product hc V).coprod (U.product hc W)) :=
  gen_product_right_distrib hc C B₀ (X := GammaNamedRVClasses hc C B₀) (gammaNamedRVClass hc C B₀)
    (gammaNamedRVClass_eq_of_iso hc C B₀) U V W

theorem gamma_product_left_distrib {n m : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n) (W : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVClass hc C B₀ ((U.coprod V).product hc W) =
      gammaNamedRVClass hc C B₀ ((U.product hc W).coprod (V.product hc W)) :=
  gen_product_left_distrib hc C B₀ (X := GammaNamedRVClasses hc C B₀) (gammaNamedRVClass hc C B₀)
    (gammaNamedRVClass_eq_of_iso hc C B₀) U V W



theorem rv_product_map_bijective {k l : ℕ} {U U' : RVObject (M := M) 𝔖 k} {V V' : RVObject (M := M) 𝔖 l}
    {f : Map U.domain U'.domain} {g : Map V.domain V'.domain}
    (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (rvProductMap f g) :=
  (rvPackToImage_bijective _ _).comp ((Map.prodMap_bijective _ _ hf hg).comp (rvUnpack_bijective _ _))

/-! ### Congruence -/

theorem gamma_product_zero_iso_left {m : ℕ} (U U' : GammaRVObjects 𝔅 𝔖 0) (V : GammaRVObjects 𝔅 𝔖 m)
    (f : ZeroRVVolumeIso U.val U'.val) (hf : f.GammaDefinable 𝔅) :
    gammaNamedRVClass hc C B₀ (U.product hc V) = gammaNamedRVClass hc C B₀ (U'.product hc V) := by
  let A := U.val.underlying
  let A' := U'.val.underlying
  let L := underlying 𝔖 m V.val
  have hA0 (u : A.obj.domain) : A'.obj.value (finiteIsoMap f.iso u) = A.obj.value u :=
    funext (fun i => i.elim0)
  exact eq_of_heq (gammaNamedRVClass_heq_of_reindex hc C B₀ rfl
    (productData 0 m U.val V.val) (productData 0 m U'.val V.val)
    (rvProductMap (U := A.obj) (U' := A'.obj) (V := L.obj) (V' := L.obj) (finiteIsoMap f.iso) (Map.id _))
    (rv_product_map_bijective C (finiteIsoMap_bijective f.iso) Function.bijective_id)
    (by
      intro x
      obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain x
      rw [rvProductMap_pair]
      change (rvProductObject A'.obj L.obj).value (rvPackPair _ _ (finiteIsoMap f.iso u) v) ∘ _ =
        (rvProductObject A.obj L.obj).value (rvPackPair _ _ u v)
      rw [rvProductObject_value_pair,rvProductObject_value_pair,hA0]
      rfl)
    (by
      intro x
      obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain x
      rw [rvProductMap_pair]
      exact (productData_density_pair 0 m U'.val V.val (finiteIsoMap f.iso u) v).trans
        ((congrArg (fun t => t * (form 𝔖 m V.val).value v) (f.density u).symm).trans
          (productData_density_pair 0 m U.val V.val u v).symm))
    (U.product hc V).property (U'.product hc V).property
    (gamma_rv_product_map_pair (k' := 0) (l' := 0) hf (gamma_rv_identity_map hc _ V.property.domain)))

theorem gamma_product_zero_iso_right {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V V' : GammaRVObjects 𝔅 𝔖 0)
    (g : ZeroRVVolumeIso V.val V'.val) (hg : g.GammaDefinable 𝔅) :
    gammaNamedRVClass hc C B₀ (U.product hc V) = gammaNamedRVClass hc C B₀ (U.product hc V') := by
  let A := underlying 𝔖 n U.val
  let L := V.val.underlying
  let L' := V'.val.underlying
  have hL0 (v : L.obj.domain) : L'.obj.value (finiteIsoMap g.iso v) = L.obj.value v :=
    funext (fun i => i.elim0)
  exact eq_of_heq (gammaNamedRVClass_heq_of_reindex hc C B₀ rfl
    (productData n 0 U.val V.val) (productData n 0 U.val V'.val)
    (rvProductMap (U := A.obj) (U' := A.obj) (V := L.obj) (V' := L'.obj) (Map.id _) (finiteIsoMap g.iso))
    (rv_product_map_bijective C Function.bijective_id (finiteIsoMap_bijective g.iso))
    (by
      intro x
      obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain x
      rw [rvProductMap_pair]
      change (rvProductObject A.obj L'.obj).value (rvPackPair _ _ u (finiteIsoMap g.iso v)) ∘ _ =
        (rvProductObject A.obj L.obj).value (rvPackPair _ _ u v)
      rw [rvProductObject_value_pair,rvProductObject_value_pair,hL0]
      rfl)
    (by
      intro x
      obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain x
      rw [rvProductMap_pair]
      exact (productData_density_pair n 0 U.val V'.val u (finiteIsoMap g.iso v)).trans
        ((congrArg (fun t => (form 𝔖 n U.val).value u * t) (g.density v).symm).trans
          (productData_density_pair n 0 U.val V.val u v).symm))
    (U.product hc V).property (U.product hc V').property
    (gamma_rv_product_map_pair (k' := 0) (l' := 0) (gamma_rv_identity_map hc _ U.property.domain) hg))

theorem gamma_named_product_congr_left {n m : ℕ} {U U' : GammaRVObjects 𝔅 𝔖 n}
    (h : gammaNamedRVClass hc C B₀ U = gammaNamedRVClass hc C B₀ U') (V : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVClass hc C B₀ (U.product hc V) = gammaNamedRVClass hc C B₀ (U'.product hc V) := by
  cases n with
  | zero =>
    obtain ⟨f,hf⟩ := Quotient.exact (s := gammaZeroRVSetoid 𝔅 𝔖) h
    exact gamma_product_zero_iso_left hc C B₀ U U' V f hf
  | succ k =>
    have hb := (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mp h
    obtain ⟨V,hV⟩ := V
    cases m with
    | succ j =>
      exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
        (hb.product_right hc 𝔇 ⟨V,(RVVolumeObject.Gamma.positive_iff V).mp hV⟩)
    | zero =>
      let Z : GammaZeroRVObjects 𝔅 𝔖 := ⟨V,(RVVolumeObject.Gamma.zero_iff V).mp hV⟩
      let P : GammaVolumeObjects 𝔅 𝔖 k := ⟨U.val,(RVVolumeObject.Gamma.positive_iff U.val).mp U.property⟩
      let P' : GammaVolumeObjects 𝔅 𝔖 k := ⟨U'.val,(RVVolumeObject.Gamma.positive_iff U'.val).mp U'.property⟩
      have hPZ := (HK.RVVolumeObject.Gamma.product (n := k+1) (m := 0) hc U.property hV)
      have hPZ' := (HK.RVVolumeObject.Gamma.product (n := k+1) (m := 0) hc U'.property hV)
      have e1 : GammaVolumeBlowupEquivalent 𝔅 𝔖 k
          ⟨HK.product 𝔖 (k+1) 0 U.val V,(RVVolumeObject.Gamma.positive_iff _).mp hPZ⟩ (P.posZeroProd hc Z) :=
        GammaVolumeBlowupEquivalent.of_iso 𝔇 𝔅 (productPositiveZeroIso hc 𝔇 U.val Z.val)
          (gamma_volume_iso_of_label_identity hc (productPositiveZeroIso hc 𝔇 U.val Z.val)
            ((RVVolumeObject.Gamma.positive_iff _).mp hPZ) rfl (fun _ => rfl))
      have e2 : GammaVolumeBlowupEquivalent 𝔅 𝔖 k (P'.posZeroProd hc Z)
          ⟨HK.product 𝔖 (k+1) 0 U'.val V,(RVVolumeObject.Gamma.positive_iff _).mp hPZ'⟩ :=
        GammaVolumeBlowupEquivalent.of_iso 𝔇 𝔅 ((productPositiveZeroIso hc 𝔇 U'.val Z.val).symm hc 𝔇)
          ((gamma_volume_iso_of_label_identity hc (productPositiveZeroIso hc 𝔇 U'.val Z.val)
            ((RVVolumeObject.Gamma.positive_iff _).mp hPZ') rfl (fun _ => rfl)).symm hc 𝔇 𝔅)
      exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
        ((e1.trans hc 𝔇 𝔅 (hb.weightedPositiveZero hc 𝔇 Z)).trans hc 𝔇 𝔅 e2)

theorem gamma_named_product_congr_right {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) {V V' : GammaRVObjects 𝔅 𝔖 m}
    (h : gammaNamedRVClass hc C B₀ V = gammaNamedRVClass hc C B₀ V') :
    gammaNamedRVClass hc C B₀ (U.product hc V) = gammaNamedRVClass hc C B₀ (U.product hc V') := by
  cases m with
  | zero =>
    obtain ⟨g,hg⟩ := Quotient.exact (s := gammaZeroRVSetoid 𝔅 𝔖) h
    exact gamma_product_zero_iso_right hc C B₀ U V V' g hg
  | succ j =>
    have hb := (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mp h
    obtain ⟨U,hU⟩ := U
    cases n with
    | succ k =>
      exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
        (hb.product_left hc 𝔇 ⟨U,(RVVolumeObject.Gamma.positive_iff U).mp hU⟩)
    | zero =>
      let Z : GammaZeroRVObjects 𝔅 𝔖 := ⟨U,(RVVolumeObject.Gamma.zero_iff U).mp hU⟩
      let P : GammaVolumeObjects 𝔅 𝔖 j := ⟨V.val,(RVVolumeObject.Gamma.positive_iff V.val).mp V.property⟩
      let P' : GammaVolumeObjects 𝔅 𝔖 j := ⟨V'.val,(RVVolumeObject.Gamma.positive_iff V'.val).mp V'.property⟩
      have hZP := (HK.RVVolumeObject.Gamma.product (n := 0) (m := j+1) hc hU V.property)
      have hZP' := (HK.RVVolumeObject.Gamma.product (n := 0) (m := j+1) hc hU V'.property)
      have e1 : GammaVolumeBlowupEquivalent 𝔅 𝔖 (0+j)
          ⟨HK.product 𝔖 0 (j+1) U V.val,(RVVolumeObject.Gamma.positive_iff _).mp hZP⟩
          ((P.zeroProd hc Z).reindexDegree (Nat.zero_add j)) :=
        GammaVolumeBlowupEquivalent.of_iso 𝔇 𝔅 (productZeroPositiveIso hc 𝔇 Z.val V.val)
          (gamma_volume_iso_of_label_identity hc (productZeroPositiveIso hc 𝔇 Z.val V.val)
            ((RVVolumeObject.Gamma.positive_iff _).mp hZP) rfl (fun _ => rfl))
      have e2 : GammaVolumeBlowupEquivalent 𝔅 𝔖 (0+j) ((P'.zeroProd hc Z).reindexDegree (Nat.zero_add j))
          ⟨HK.product 𝔖 0 (j+1) U V'.val,(RVVolumeObject.Gamma.positive_iff _).mp hZP'⟩ :=
        GammaVolumeBlowupEquivalent.of_iso 𝔇 𝔅 ((productZeroPositiveIso hc 𝔇 Z.val V'.val).symm hc 𝔇)
          ((gamma_volume_iso_of_label_identity hc (productZeroPositiveIso hc 𝔇 Z.val V'.val)
            ((RVVolumeObject.Gamma.positive_iff _).mp hZP') rfl (fun _ => rfl)).symm hc 𝔇 𝔅)
      exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
        ((e1.trans hc 𝔇 𝔅 ((hb.weightedZero hc 𝔇 Z).reindexDegree hc 𝔇 (Nat.zero_add j))).trans hc 𝔇 𝔅 e2)

theorem gamma_named_product_congr {n m : ℕ} {U U' : GammaRVObjects 𝔅 𝔖 n} {V V' : GammaRVObjects 𝔅 𝔖 m}
    (hU : gammaNamedRVClass hc C B₀ U = gammaNamedRVClass hc C B₀ U')
    (hV : gammaNamedRVClass hc C B₀ V = gammaNamedRVClass hc C B₀ V') :
    gammaNamedRVClass hc C B₀ (U.product hc V) = gammaNamedRVClass hc C B₀ (U'.product hc V') :=
  (gamma_named_product_congr_left hc C B₀ hU V).trans (gamma_named_product_congr_right hc C B₀ U' hV)

/-! ### The graded semiring -/

/-- A chosen Gamma representative of a Gamma-named class. -/
def gammaNamedRVRep {n : ℕ} (a : GammaNamedRVClasses hc C B₀ n) : GammaRVObjects 𝔅 𝔖 n :=
  Function.surjInv (gammaNamedRVClass_surjective hc C B₀ n) a

theorem gammaNamedRVRep_class {n : ℕ} (a : GammaNamedRVClasses hc C B₀ n) :
    gammaNamedRVClass hc C B₀ (gammaNamedRVRep hc C B₀ a) = a :=
  Function.surjInv_eq _ a

/-- Product of Gamma-named RV classes: the class of the actual product. -/
def gammaNamedRVMul {n m : ℕ} (a : GammaNamedRVClasses hc C B₀ n) (b : GammaNamedRVClasses hc C B₀ m) :
    GammaNamedRVClasses hc C B₀ (n+m) :=
  gammaNamedRVClass hc C B₀ ((gammaNamedRVRep hc C B₀ a).product hc (gammaNamedRVRep hc C B₀ b))

theorem gammaNamedRVMul_class {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVMul hc C B₀ (gammaNamedRVClass hc C B₀ U) (gammaNamedRVClass hc C B₀ V) =
      gammaNamedRVClass hc C B₀ (U.product hc V) :=
  gamma_named_product_congr hc C B₀ (gammaNamedRVRep_class hc C B₀ _) (gammaNamedRVRep_class hc C B₀ _)

theorem gammaNamedRV_zero_eq (n : ℕ) :
    (0 : GammaNamedRVClasses hc C B₀ n) = gammaNamedRVClass hc C B₀ (gammaEmpty C B₀ n) := by
  cases n <;> rfl

theorem gammaNamedRV_add_eq {n : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVClass hc C B₀ U + gammaNamedRVClass hc C B₀ V =
      gammaNamedRVClass hc C B₀ (U.coprod V) :=
  (gammaNamedRVClass_coprod hc C B₀ U V).symm

theorem gamma_named_class_induction {n : ℕ} {P : GammaNamedRVClasses hc C B₀ n → Prop}
    (h : ∀ U, P (gammaNamedRVClass hc C B₀ U)) (a : GammaNamedRVClasses hc C B₀ n) : P a := by
  obtain ⟨U,rfl⟩ := gammaNamedRVClass_surjective hc C B₀ n a
  exact h U

instance gammaNamedRVClassesGMul : GradedMonoid.GMul (GammaNamedRVClasses hc C B₀) :=
  ⟨fun {_ _} a b => gammaNamedRVMul hc C B₀ a b⟩

instance gammaNamedRVClassesGOne : GradedMonoid.GOne (GammaNamedRVClasses hc C B₀) :=
  ⟨gammaNamedRVClass hc C B₀ (gammaUnit hc C B₀)⟩

theorem gammaNamedRV_mul_def {n m : ℕ} (a : GammaNamedRVClasses hc C B₀ n) (b : GammaNamedRVClasses hc C B₀ m) :
    GradedMonoid.GMul.mul a b = gammaNamedRVMul hc C B₀ a b := rfl

instance gammaNamedRVClassesGMonoid : GradedMonoid.GMonoid (GammaNamedRVClasses hc C B₀) where
  one_mul a := by
    obtain ⟨n,a⟩ := a
    apply Sigma.ext (Nat.zero_add n)
    induction a using gamma_named_class_induction hc C B₀ with
    | h U =>
      change HEq (gammaNamedRVMul hc C B₀ (gammaNamedRVClass hc C B₀ (gammaUnit hc C B₀))
        (gammaNamedRVClass hc C B₀ U)) (gammaNamedRVClass hc C B₀ U)
      rw [gammaNamedRVMul_class]
      exact gamma_product_left_unit hc C B₀ U
  mul_one a := by
    obtain ⟨n,a⟩ := a
    apply Sigma.ext (Nat.add_zero n)
    induction a using gamma_named_class_induction hc C B₀ with
    | h U =>
      change HEq (gammaNamedRVMul hc C B₀ (gammaNamedRVClass hc C B₀ U)
        (gammaNamedRVClass hc C B₀ (gammaUnit hc C B₀))) (gammaNamedRVClass hc C B₀ U)
      rw [gammaNamedRVMul_class]
      exact heq_of_eq (gamma_product_right_unit hc C B₀ U)
  mul_assoc a b c := by
    obtain ⟨n,a⟩ := a
    obtain ⟨m,b⟩ := b
    obtain ⟨l,c⟩ := c
    apply Sigma.ext (Nat.add_assoc n m l)
    induction a using gamma_named_class_induction hc C B₀ with
    | h U =>
      induction b using gamma_named_class_induction hc C B₀ with
      | h V =>
        induction c using gamma_named_class_induction hc C B₀ with
        | h W =>
          change HEq (gammaNamedRVMul hc C B₀ (gammaNamedRVMul hc C B₀ (gammaNamedRVClass hc C B₀ U)
              (gammaNamedRVClass hc C B₀ V)) (gammaNamedRVClass hc C B₀ W))
            (gammaNamedRVMul hc C B₀ (gammaNamedRVClass hc C B₀ U)
              (gammaNamedRVMul hc C B₀ (gammaNamedRVClass hc C B₀ V) (gammaNamedRVClass hc C B₀ W)))
          rw [gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRVMul_class]
          exact gamma_product_assoc hc C B₀ U V W

instance gammaNamedRVClassesGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (GammaNamedRVClasses hc C B₀) where
  mul_zero {n m} a := by
    induction a using gamma_named_class_induction hc C B₀ with
    | h U =>
      rw [gammaNamedRV_mul_def,gammaNamedRV_zero_eq,gammaNamedRVMul_class,gammaNamedRV_zero_eq]
      exact gamma_product_right_zero hc C B₀ U
  zero_mul {n m} b := by
    induction b using gamma_named_class_induction hc C B₀ with
    | h V =>
      rw [gammaNamedRV_mul_def,gammaNamedRV_zero_eq,gammaNamedRVMul_class,gammaNamedRV_zero_eq]
      exact gamma_product_left_zero hc C B₀ V
  mul_add {n m} a b c := by
    induction a using gamma_named_class_induction hc C B₀ with
    | h U =>
      induction b using gamma_named_class_induction hc C B₀ with
      | h V =>
        induction c using gamma_named_class_induction hc C B₀ with
        | h W =>
          rw [gammaNamedRV_mul_def,gammaNamedRV_mul_def,gammaNamedRV_mul_def,gammaNamedRV_add_eq,
            gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRV_add_eq]
          exact gamma_product_right_distrib hc C B₀ U V W
  add_mul {n m} a b c := by
    induction a using gamma_named_class_induction hc C B₀ with
    | h U =>
      induction b using gamma_named_class_induction hc C B₀ with
      | h V =>
        induction c using gamma_named_class_induction hc C B₀ with
        | h W =>
          rw [gammaNamedRV_mul_def,gammaNamedRV_mul_def,gammaNamedRV_mul_def,gammaNamedRV_add_eq,
            gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRV_add_eq]
          exact gamma_product_left_distrib hc C B₀ U V W

instance gammaNamedRVClassesGSemiring : DirectSum.GSemiring (GammaNamedRVClasses hc C B₀) where
  natCast n :=
    letI := gammaNamedRVClassesAddCommMonoid hc C B₀ 0
    (n • gammaNamedRVClass hc C B₀ (gammaUnit hc C B₀) : GammaNamedRVClasses hc C B₀ 0)
  natCast_zero :=
    letI := gammaNamedRVClassesAddCommMonoid hc C B₀ 0
    zero_nsmul _
  natCast_succ n := by
    letI := gammaNamedRVClassesAddCommMonoid hc C B₀ 0
    simp only [succ_nsmul,one_nsmul]
    rfl

/-- The graded semiring of Gamma RV volume classes in the context `C` over the base `B₀`. -/
abbrev GammaNamedRVSemiring := DirectSum ℕ (GammaNamedRVClasses hc C B₀)

end IntegrationInACVF.Section7.HK.Ctx
