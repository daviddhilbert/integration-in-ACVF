import Integration7.GammaNamedZeroBlowupProducts

/-! The graded semiring of Gamma-named RV classes. Actual products descend
to Gamma-named classes: Gamma degree-zero isomorphisms act factorwise, and
Gamma blowups multiply with positive or weighted degree-zero Gamma factors
on either side. The unit, zero, associativity and distributivity laws are
the actual relabelling isomorphisms, which are Gamma. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem rv_product_map_bijective {k l : ℕ} {U U' : RVObject (M := M) 𝔖 k} {V V' : RVObject (M := M) 𝔖 l}
    {f : Map U.domain U'.domain} {g : Map V.domain V'.domain}
    (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (rvProductMap f g) :=
  (rvPackToImage_bijective _ _).comp ((Map.prodMap_bijective _ _ hf hg).comp (rvUnpack_bijective _ _))

/-! ### Congruence -/

theorem gamma_product_zero_iso_left {m : ℕ} (U U' : GammaRVObjects 𝔅 𝔖 0) (V : GammaRVObjects 𝔅 𝔖 m)
    (f : ZeroRVVolumeIso U.val U'.val) (hf : f.GammaDefinable 𝔅) :
    gammaNamedRVClass hc C Ξ hΞ (U.product hc V) = gammaNamedRVClass hc C Ξ hΞ (U'.product hc V) := by
  let A := U.val.underlying
  let A' := U'.val.underlying
  let L := underlying 𝔖 m V.val
  have hA0 (u : A.obj.domain) : A'.obj.value (finiteIsoMap f.iso u) = A.obj.value u :=
    funext (fun i => i.elim0)
  exact eq_of_heq (gammaNamedRVClass_heq_of_reindex hc C Ξ hΞ rfl
    (productData 0 m U.val V.val) (productData 0 m U'.val V.val)
    (rvProductMap (U := A.obj) (U' := A'.obj) (V := L.obj) (V' := L.obj) (finiteIsoMap f.iso) (Map.id _))
    (rv_product_map_bijective C Ξ hΞ (finiteIsoMap_bijective f.iso) Function.bijective_id)
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
    gammaNamedRVClass hc C Ξ hΞ (U.product hc V) = gammaNamedRVClass hc C Ξ hΞ (U.product hc V') := by
  let A := underlying 𝔖 n U.val
  let L := V.val.underlying
  let L' := V'.val.underlying
  have hL0 (v : L.obj.domain) : L'.obj.value (finiteIsoMap g.iso v) = L.obj.value v :=
    funext (fun i => i.elim0)
  exact eq_of_heq (gammaNamedRVClass_heq_of_reindex hc C Ξ hΞ rfl
    (productData n 0 U.val V.val) (productData n 0 U.val V'.val)
    (rvProductMap (U := A.obj) (U' := A.obj) (V := L.obj) (V' := L'.obj) (Map.id _) (finiteIsoMap g.iso))
    (rv_product_map_bijective C Ξ hΞ Function.bijective_id (finiteIsoMap_bijective g.iso))
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
    (h : gammaNamedRVClass hc C Ξ hΞ U = gammaNamedRVClass hc C Ξ hΞ U') (V : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVClass hc C Ξ hΞ (U.product hc V) = gammaNamedRVClass hc C Ξ hΞ (U'.product hc V) := by
  cases n with
  | zero =>
    obtain ⟨f,hf⟩ := Quotient.exact (s := gammaZeroRVSetoid 𝔅 𝔖) h
    exact gamma_product_zero_iso_left hc C Ξ hΞ U U' V f hf
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
    (h : gammaNamedRVClass hc C Ξ hΞ V = gammaNamedRVClass hc C Ξ hΞ V') :
    gammaNamedRVClass hc C Ξ hΞ (U.product hc V) = gammaNamedRVClass hc C Ξ hΞ (U.product hc V') := by
  cases m with
  | zero =>
    obtain ⟨g,hg⟩ := Quotient.exact (s := gammaZeroRVSetoid 𝔅 𝔖) h
    exact gamma_product_zero_iso_right hc C Ξ hΞ U V V' g hg
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
    (hU : gammaNamedRVClass hc C Ξ hΞ U = gammaNamedRVClass hc C Ξ hΞ U')
    (hV : gammaNamedRVClass hc C Ξ hΞ V = gammaNamedRVClass hc C Ξ hΞ V') :
    gammaNamedRVClass hc C Ξ hΞ (U.product hc V) = gammaNamedRVClass hc C Ξ hΞ (U'.product hc V') :=
  (gamma_named_product_congr_left hc C Ξ hΞ hU V).trans (gamma_named_product_congr_right hc C Ξ hΞ U' hV)

/-! ### The graded semiring -/

/-- A chosen Gamma representative of a Gamma-named class. -/
def gammaNamedRVRep {n : ℕ} (a : GammaNamedRVClasses hc C Ξ hΞ n) : GammaRVObjects 𝔅 𝔖 n :=
  Function.surjInv (gammaNamedRVClass_surjective hc C Ξ hΞ n) a

theorem gammaNamedRVRep_class {n : ℕ} (a : GammaNamedRVClasses hc C Ξ hΞ n) :
    gammaNamedRVClass hc C Ξ hΞ (gammaNamedRVRep hc C Ξ hΞ a) = a :=
  Function.surjInv_eq _ a

/-- Product of Gamma-named RV classes: the class of the actual product. -/
def gammaNamedRVMul {n m : ℕ} (a : GammaNamedRVClasses hc C Ξ hΞ n) (b : GammaNamedRVClasses hc C Ξ hΞ m) :
    GammaNamedRVClasses hc C Ξ hΞ (n+m) :=
  gammaNamedRVClass hc C Ξ hΞ ((gammaNamedRVRep hc C Ξ hΞ a).product hc (gammaNamedRVRep hc C Ξ hΞ b))

theorem gammaNamedRVMul_class {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVClass hc C Ξ hΞ U) (gammaNamedRVClass hc C Ξ hΞ V) =
      gammaNamedRVClass hc C Ξ hΞ (U.product hc V) :=
  gamma_named_product_congr hc C Ξ hΞ (gammaNamedRVRep_class hc C Ξ hΞ _) (gammaNamedRVRep_class hc C Ξ hΞ _)

theorem gammaNamedRV_zero_eq (n : ℕ) :
    (0 : GammaNamedRVClasses hc C Ξ hΞ n) = gammaNamedRVClass hc C Ξ hΞ (gammaEmpty C Ξ hΞ n) := by
  cases n <;> rfl

theorem gammaNamedRV_add_eq {n : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVClass hc C Ξ hΞ U + gammaNamedRVClass hc C Ξ hΞ V =
      gammaNamedRVClass hc C Ξ hΞ (U.coprod V) :=
  (gammaNamedRVClass_coprod hc C Ξ hΞ U V).symm

theorem gamma_named_class_induction {n : ℕ} {P : GammaNamedRVClasses hc C Ξ hΞ n → Prop}
    (h : ∀ U, P (gammaNamedRVClass hc C Ξ hΞ U)) (a : GammaNamedRVClasses hc C Ξ hΞ n) : P a := by
  obtain ⟨U,rfl⟩ := gammaNamedRVClass_surjective hc C Ξ hΞ n a
  exact h U

instance gammaNamedRVClassesGMul : GradedMonoid.GMul (GammaNamedRVClasses hc C Ξ hΞ) :=
  ⟨fun {_ _} a b => gammaNamedRVMul hc C Ξ hΞ a b⟩

instance gammaNamedRVClassesGOne : GradedMonoid.GOne (GammaNamedRVClasses hc C Ξ hΞ) :=
  ⟨gammaNamedRVClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ)⟩

theorem gammaNamedRV_mul_def {n m : ℕ} (a : GammaNamedRVClasses hc C Ξ hΞ n) (b : GammaNamedRVClasses hc C Ξ hΞ m) :
    GradedMonoid.GMul.mul a b = gammaNamedRVMul hc C Ξ hΞ a b := rfl

instance gammaNamedRVClassesGMonoid : GradedMonoid.GMonoid (GammaNamedRVClasses hc C Ξ hΞ) where
  one_mul a := by
    obtain ⟨n,a⟩ := a
    apply Sigma.ext (Nat.zero_add n)
    induction a using gamma_named_class_induction hc C Ξ hΞ with
    | h U =>
      change HEq (gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ))
        (gammaNamedRVClass hc C Ξ hΞ U)) (gammaNamedRVClass hc C Ξ hΞ U)
      rw [gammaNamedRVMul_class]
      exact gamma_product_left_unit hc C Ξ hΞ U
  mul_one a := by
    obtain ⟨n,a⟩ := a
    apply Sigma.ext (Nat.add_zero n)
    induction a using gamma_named_class_induction hc C Ξ hΞ with
    | h U =>
      change HEq (gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVClass hc C Ξ hΞ U)
        (gammaNamedRVClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ))) (gammaNamedRVClass hc C Ξ hΞ U)
      rw [gammaNamedRVMul_class]
      exact heq_of_eq (gamma_product_right_unit hc C Ξ hΞ U)
  mul_assoc a b c := by
    obtain ⟨n,a⟩ := a
    obtain ⟨m,b⟩ := b
    obtain ⟨l,c⟩ := c
    apply Sigma.ext (Nat.add_assoc n m l)
    induction a using gamma_named_class_induction hc C Ξ hΞ with
    | h U =>
      induction b using gamma_named_class_induction hc C Ξ hΞ with
      | h V =>
        induction c using gamma_named_class_induction hc C Ξ hΞ with
        | h W =>
          change HEq (gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVClass hc C Ξ hΞ U)
              (gammaNamedRVClass hc C Ξ hΞ V)) (gammaNamedRVClass hc C Ξ hΞ W))
            (gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVClass hc C Ξ hΞ U)
              (gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVClass hc C Ξ hΞ V) (gammaNamedRVClass hc C Ξ hΞ W)))
          rw [gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRVMul_class]
          exact gamma_product_assoc hc C Ξ hΞ U V W

instance gammaNamedRVClassesGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (GammaNamedRVClasses hc C Ξ hΞ) where
  mul_zero {n m} a := by
    induction a using gamma_named_class_induction hc C Ξ hΞ with
    | h U =>
      rw [gammaNamedRV_mul_def,gammaNamedRV_zero_eq,gammaNamedRVMul_class,gammaNamedRV_zero_eq]
      exact gamma_product_right_zero hc C Ξ hΞ U
  zero_mul {n m} b := by
    induction b using gamma_named_class_induction hc C Ξ hΞ with
    | h V =>
      rw [gammaNamedRV_mul_def,gammaNamedRV_zero_eq,gammaNamedRVMul_class,gammaNamedRV_zero_eq]
      exact gamma_product_left_zero hc C Ξ hΞ V
  mul_add {n m} a b c := by
    induction a using gamma_named_class_induction hc C Ξ hΞ with
    | h U =>
      induction b using gamma_named_class_induction hc C Ξ hΞ with
      | h V =>
        induction c using gamma_named_class_induction hc C Ξ hΞ with
        | h W =>
          rw [gammaNamedRV_mul_def,gammaNamedRV_mul_def,gammaNamedRV_mul_def,gammaNamedRV_add_eq,
            gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRV_add_eq]
          exact gamma_product_right_distrib hc C Ξ hΞ U V W
  add_mul {n m} a b c := by
    induction a using gamma_named_class_induction hc C Ξ hΞ with
    | h U =>
      induction b using gamma_named_class_induction hc C Ξ hΞ with
      | h V =>
        induction c using gamma_named_class_induction hc C Ξ hΞ with
        | h W =>
          rw [gammaNamedRV_mul_def,gammaNamedRV_mul_def,gammaNamedRV_mul_def,gammaNamedRV_add_eq,
            gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRVMul_class,gammaNamedRV_add_eq]
          exact gamma_product_left_distrib hc C Ξ hΞ U V W

instance gammaNamedRVClassesGSemiring : DirectSum.GSemiring (GammaNamedRVClasses hc C Ξ hΞ) where
  natCast n :=
    letI := gammaNamedRVClassesAddCommMonoid hc C Ξ hΞ 0
    (n • gammaNamedRVClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ) : GammaNamedRVClasses hc C Ξ hΞ 0)
  natCast_zero :=
    letI := gammaNamedRVClassesAddCommMonoid hc C Ξ hΞ 0
    zero_nsmul _
  natCast_succ n := by
    letI := gammaNamedRVClassesAddCommMonoid hc C Ξ hΞ 0
    simp only [succ_nsmul,one_nsmul]
    rfl

/-- The graded semiring of Gamma-named RV volume classes over `⟨C.base, Ξ⟩`. -/
abbrev GammaNamedRVSemiring := DirectSum ℕ (GammaNamedRVClasses hc C Ξ hΞ)

end IntegrationInACVF.Section7.HK
