import Integration7.GammaNamedTheorem710
import Integration7.GammaVolumeIsomorphismClasses
import Integration7.GammaVolumeCoproductCharts
import Integration7.GammaVolumeCoproductAssociativity

/-! The graded semiring of Gamma-named RV isomorphism classes (Gamma objects
modulo Gamma isomorphisms, before blowups) and its surjective graded
projection to the Gamma-named blowup classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (B : Base (M := M))

instance gammaVolumeIsoClassesAdd (k : ℕ) : Add (GammaVolumeIsoClasses hc C B k) :=
  ⟨Quotient.map₂ GammaVolumeObjects.coprod (fun _ _ ⟨f,hf⟩ _ _ ⟨g,hg⟩ =>
    ⟨f.coprod hc C g,RVVolumeIso.GammaDefinable.coprod hc C B hf hg⟩)⟩

instance gammaVolumeIsoClassesZero (k : ℕ) : Zero (GammaVolumeIsoClasses hc C B k) :=
  ⟨gammaVolumeIsoClass hc C B (GammaVolumeObjects.empty B (C.base : Set M) k)⟩

instance gammaVolumeIsoClassesAddCommMonoid (k : ℕ) : AddCommMonoid (GammaVolumeIsoClasses hc C B k) where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun U V W =>
    gammaVolumeIsoClass_iso hc C B (volumeCoprodAssoc hc C U.val V.val W.val)
      (gamma_volume_coprod_assoc hc C U.property V.property W.property))
  add_comm a b := Quotient.inductionOn₂ a b (fun U V =>
    gammaVolumeIsoClass_iso hc C B (volumeCoprodSwap hc C U.val V.val)
      (gamma_volume_coprod_swap hc C U.property V.property))
  zero_add a := Quotient.inductionOn a (fun U =>
    gammaVolumeIsoClass_iso hc C B (volumeCoprodLeftUnit hc C U.val)
      (gamma_volume_coprod_left_unit hc C U.property))
  add_zero a := Quotient.inductionOn a (fun U =>
    gammaVolumeIsoClass_iso hc C B (volumeCoprodRightUnit hc C U.val)
      (gamma_volume_coprod_right_unit hc C U.property))
  nsmul := nsmulRec

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- Gamma-named RV isomorphism classes in every degree. -/
abbrev GammaNamedRVIsoClasses : ℕ → Type
  | 0 => GammaZeroRVClasses (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M)
  | k+1 => GammaVolumeIsoClasses hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) k

instance gammaNamedRVIsoClassesAddCommMonoid : (n : ℕ) → AddCommMonoid (GammaNamedRVIsoClasses hc C Ξ hΞ n)
  | 0 => gammaZeroRVAddCommMonoid hc
  | _+1 => inferInstance

def gammaNamedRVIsoClass : {n : ℕ} → GammaRVObjects 𝔅 𝔖 n → GammaNamedRVIsoClasses hc C Ξ hΞ n
  | 0, U => Quotient.mk _ ⟨U.val,(RVVolumeObject.Gamma.zero_iff U.val).mp U.property⟩
  | _+1, U => gammaVolumeIsoClass hc 𝔇 𝔅 ⟨U.val,(RVVolumeObject.Gamma.positive_iff U.val).mp U.property⟩

theorem gammaNamedRVIsoClass_surjective (n : ℕ) :
    Function.Surjective (gammaNamedRVIsoClass hc C Ξ hΞ (n := n)) := by
  cases n with
  | zero =>
    intro a
    induction a using Quotient.inductionOn with
    | h U => exact ⟨⟨U.val,(RVVolumeObject.Gamma.zero_iff U.val).mpr U.property⟩,rfl⟩
  | succ k =>
    intro a
    induction a using Quotient.inductionOn with
    | h U => exact ⟨⟨U.val,(RVVolumeObject.Gamma.positive_iff U.val).mpr U.property⟩,rfl⟩

theorem gammaNamedRVIsoClass_eq_of_iso {n : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n)
    (e : rvVolumeIsoInDegree 𝔖 n U.val V.val) (he : IsoGamma n e 𝔅) :
    gammaNamedRVIsoClass hc C Ξ hΞ U = gammaNamedRVIsoClass hc C Ξ hΞ V := by
  cases n with
  | zero => exact Quotient.sound ⟨e,he⟩
  | succ k => exact gammaVolumeIsoClass_iso hc 𝔇 𝔅 e he

theorem gammaNamedRVIsoClass_coprod {n : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVIsoClass hc C Ξ hΞ (U.coprod V) =
      gammaNamedRVIsoClass hc C Ξ hΞ U + gammaNamedRVIsoClass hc C Ξ hΞ V := by
  cases n <;> rfl

theorem gammaNamedRVIso_zero_eq (n : ℕ) :
    (0 : GammaNamedRVIsoClasses hc C Ξ hΞ n) = gammaNamedRVIsoClass hc C Ξ hΞ (gammaEmpty C Ξ hΞ n) := by
  cases n <;> rfl

/-! ### Products of Gamma isomorphisms -/

theorem gamma_zero_zero_product_iso {U U' V V' : ZeroRVVolumeObject (M := M) 𝔖}
    {f : ZeroRVVolumeIso U U'} {g : ZeroRVVolumeIso V V'} (hf : f.GammaDefinable 𝔅) (hg : g.GammaDefinable 𝔅) :
    (zeroZeroProductIso f g).GammaDefinable 𝔅 :=
  (gamma_rv_product_map_pair (k' := 0) (l' := 0) hf hg).congr (fun _ => rfl)

include hc in
theorem gamma_reindex_iso_equiv {a b : ℕ} (h : a = b) {U V : GammaVolumeObjects 𝔅 𝔖 b}
    (e : RVVolumeIso U.val V.val) (he : e.GammaDefinable 𝔅) :
    ∃ e' : RVVolumeIso (U.reindexDegree h).val (V.reindexDegree h).val, e'.GammaDefinable 𝔅 := by
  cases h
  have hU := gamma_volume_iso_of_label_identity hc (volumeCastReindexIso hc 𝔇 U.val rfl)
    (U.property.reindexDegree rfl) rfl (fun _ => rfl)
  have hV := gamma_volume_iso_of_label_identity hc (volumeCastReindexIso hc 𝔇 V.val rfl)
    (V.property.reindexDegree rfl) rfl (fun _ => rfl)
  exact ⟨((volumeCastReindexIso hc 𝔇 U.val rfl).trans hc 𝔇 e).trans hc 𝔇
    ((volumeCastReindexIso hc 𝔇 V.val rfl).symm hc 𝔇),
    (hU.trans hc 𝔇 𝔅 he).trans hc 𝔇 𝔅 (hV.symm hc 𝔇 𝔅)⟩

theorem gamma_named_product_iso_congr {n m : ℕ} {U U' : GammaRVObjects 𝔅 𝔖 n} {V V' : GammaRVObjects 𝔅 𝔖 m}
    (hU : gammaNamedRVIsoClass hc C Ξ hΞ U = gammaNamedRVIsoClass hc C Ξ hΞ U')
    (hV : gammaNamedRVIsoClass hc C Ξ hΞ V = gammaNamedRVIsoClass hc C Ξ hΞ V') :
    gammaNamedRVIsoClass hc C Ξ hΞ (U.product hc V) = gammaNamedRVIsoClass hc C Ξ hΞ (U'.product hc V') := by
  obtain ⟨U,hU0⟩ := U
  obtain ⟨U',hU0'⟩ := U'
  obtain ⟨V,hV0⟩ := V
  obtain ⟨V',hV0'⟩ := V'
  cases n with
  | zero =>
    obtain ⟨f,hf⟩ := Quotient.exact (s := gammaZeroRVSetoid 𝔅 𝔖) hU
    cases m with
    | zero =>
      obtain ⟨g,hg⟩ := Quotient.exact (s := gammaZeroRVSetoid 𝔅 𝔖) hV
      exact Quotient.sound ⟨zeroZeroProductIso f g,gamma_zero_zero_product_iso C Ξ hΞ hf hg⟩
    | succ j =>
      obtain ⟨g,hg⟩ := (gammaVolumeIsoClass_eq_iff hc 𝔇 𝔅).mp hV
      let Z : GammaZeroRVObjects 𝔅 𝔖 := ⟨U,(RVVolumeObject.Gamma.zero_iff U).mp hU0⟩
      let Z' : GammaZeroRVObjects 𝔅 𝔖 := ⟨U',(RVVolumeObject.Gamma.zero_iff U').mp hU0'⟩
      let P : GammaVolumeObjects 𝔅 𝔖 j := ⟨V,(RVVolumeObject.Gamma.positive_iff V).mp hV0⟩
      let P' : GammaVolumeObjects 𝔅 𝔖 j := ⟨V',(RVVolumeObject.Gamma.positive_iff V').mp hV0'⟩
      have hZP := HK.RVVolumeObject.Gamma.product (n := 0) (m := j+1) hc hU0 hV0
      have hZP' := HK.RVVolumeObject.Gamma.product (n := 0) (m := j+1) hc hU0' hV0'
      obtain ⟨e2,he2⟩ := gamma_reindex_iso_equiv hc C Ξ hΞ (Nat.zero_add j) (U := P.zeroProd hc Z)
        (V := P'.zeroProd hc Z') (zeroProductIso hc 𝔇 f g)
        (gamma_zero_product_iso hc 𝔇 P.property P'.property Z.property Z'.property hf hg)
      apply (gammaVolumeIsoClass_eq_iff hc 𝔇 𝔅).mpr
      exact ⟨((productZeroPositiveIso hc 𝔇 U V).trans hc 𝔇 e2).trans hc 𝔇
        ((productZeroPositiveIso hc 𝔇 U' V').symm hc 𝔇),
        ((gamma_volume_iso_of_label_identity hc (productZeroPositiveIso hc 𝔇 U V)
          ((RVVolumeObject.Gamma.positive_iff _).mp hZP) rfl (fun _ => rfl)).trans hc 𝔇 𝔅 he2).trans hc 𝔇 𝔅
          ((gamma_volume_iso_of_label_identity hc (productZeroPositiveIso hc 𝔇 U' V')
            ((RVVolumeObject.Gamma.positive_iff _).mp hZP') rfl (fun _ => rfl)).symm hc 𝔇 𝔅)⟩
  | succ k =>
    obtain ⟨f,hf⟩ := (gammaVolumeIsoClass_eq_iff hc 𝔇 𝔅).mp hU
    cases m with
    | succ j =>
      obtain ⟨g,hg⟩ := (gammaVolumeIsoClass_eq_iff hc 𝔇 𝔅).mp hV
      exact (gammaVolumeIsoClass_eq_iff hc 𝔇 𝔅).mpr ⟨f.prod hc 𝔇 g,RVVolumeIso.GammaDefinable.prod hc 𝔇 hf hg⟩
    | zero =>
      obtain ⟨g,hg⟩ := Quotient.exact (s := gammaZeroRVSetoid 𝔅 𝔖) hV
      have hPZ := HK.RVVolumeObject.Gamma.product (n := k+1) (m := 0) hc hU0 hV0
      have hPZ' := HK.RVVolumeObject.Gamma.product (n := k+1) (m := 0) hc hU0' hV0'
      apply (gammaVolumeIsoClass_eq_iff hc 𝔇 𝔅).mpr
      exact ⟨((productPositiveZeroIso hc 𝔇 U V).trans hc 𝔇 (positiveZeroProductIso hc 𝔇 f g)).trans hc 𝔇
        ((productPositiveZeroIso hc 𝔇 U' V').symm hc 𝔇),
        ((gamma_volume_iso_of_label_identity hc (productPositiveZeroIso hc 𝔇 U V)
          ((RVVolumeObject.Gamma.positive_iff _).mp hPZ) rfl (fun _ => rfl)).trans hc 𝔇 𝔅
          (gamma_positive_zero_product_iso hc 𝔇 hf hg)).trans hc 𝔇 𝔅
          ((gamma_volume_iso_of_label_identity hc (productPositiveZeroIso hc 𝔇 U' V')
            ((RVVolumeObject.Gamma.positive_iff _).mp hPZ') rfl (fun _ => rfl)).symm hc 𝔇 𝔅)⟩

/-! ### The graded semiring of isomorphism classes -/

def gammaNamedRVIsoRep {n : ℕ} (a : GammaNamedRVIsoClasses hc C Ξ hΞ n) : GammaRVObjects 𝔅 𝔖 n :=
  Function.surjInv (gammaNamedRVIsoClass_surjective hc C Ξ hΞ n) a

def gammaNamedRVIsoMul {n m : ℕ} (a : GammaNamedRVIsoClasses hc C Ξ hΞ n)
    (b : GammaNamedRVIsoClasses hc C Ξ hΞ m) : GammaNamedRVIsoClasses hc C Ξ hΞ (n+m) :=
  gammaNamedRVIsoClass hc C Ξ hΞ ((gammaNamedRVIsoRep hc C Ξ hΞ a).product hc (gammaNamedRVIsoRep hc C Ξ hΞ b))

theorem gammaNamedRVIsoMul_class {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVIsoMul hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ U) (gammaNamedRVIsoClass hc C Ξ hΞ V) =
      gammaNamedRVIsoClass hc C Ξ hΞ (U.product hc V) :=
  gamma_named_product_iso_congr hc C Ξ hΞ (Function.surjInv_eq _ _) (Function.surjInv_eq _ _)

theorem gamma_named_iso_class_induction {n : ℕ} {P : GammaNamedRVIsoClasses hc C Ξ hΞ n → Prop}
    (h : ∀ U, P (gammaNamedRVIsoClass hc C Ξ hΞ U)) (a : GammaNamedRVIsoClasses hc C Ξ hΞ n) : P a := by
  obtain ⟨U,rfl⟩ := gammaNamedRVIsoClass_surjective hc C Ξ hΞ n a
  exact h U

instance gammaNamedRVIsoClassesGMul : GradedMonoid.GMul (GammaNamedRVIsoClasses hc C Ξ hΞ) :=
  ⟨fun {_ _} a b => gammaNamedRVIsoMul hc C Ξ hΞ a b⟩

instance gammaNamedRVIsoClassesGOne : GradedMonoid.GOne (GammaNamedRVIsoClasses hc C Ξ hΞ) :=
  ⟨gammaNamedRVIsoClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ)⟩

theorem gammaNamedRVIso_mul_def {n m : ℕ} (a : GammaNamedRVIsoClasses hc C Ξ hΞ n)
    (b : GammaNamedRVIsoClasses hc C Ξ hΞ m) :
    GradedMonoid.GMul.mul a b = gammaNamedRVIsoMul hc C Ξ hΞ a b := rfl

theorem gammaNamedRVIsoClass_eq_of_iso' {n : ℕ} (U V : GammaRVObjects (gammaNamedBase C Ξ)
    ((gammaNamedCodeContext C Ξ hΞ).base : Set M) n)
    (e : rvVolumeIsoInDegree ((gammaNamedCodeContext C Ξ hΞ).base : Set M) n U.val V.val)
    (he : IsoGamma n e (gammaNamedBase C Ξ)) :
    gammaNamedRVIsoClass hc C Ξ hΞ U = gammaNamedRVIsoClass hc C Ξ hΞ V :=
  gammaNamedRVIsoClass_eq_of_iso hc C Ξ hΞ U V e he

instance gammaNamedRVIsoClassesGMonoid : GradedMonoid.GMonoid (GammaNamedRVIsoClasses hc C Ξ hΞ) where
  one_mul a := by
    obtain ⟨n,a⟩ := a
    apply Sigma.ext (Nat.zero_add n)
    induction a using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h U =>
      change HEq (gammaNamedRVIsoMul hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ))
        (gammaNamedRVIsoClass hc C Ξ hΞ U)) (gammaNamedRVIsoClass hc C Ξ hΞ U)
      rw [gammaNamedRVIsoMul_class]
      exact gen_product_left_unit hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ)
        (gammaNamedRVIsoClass_eq_of_iso' hc C Ξ hΞ) U
  mul_one a := by
    obtain ⟨n,a⟩ := a
    apply Sigma.ext (Nat.add_zero n)
    induction a using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h U =>
      change HEq (gammaNamedRVIsoMul hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ U)
        (gammaNamedRVIsoClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ))) (gammaNamedRVIsoClass hc C Ξ hΞ U)
      rw [gammaNamedRVIsoMul_class]
      exact heq_of_eq (gen_product_right_unit hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ)
        (gammaNamedRVIsoClass_eq_of_iso' hc C Ξ hΞ) U)
  mul_assoc a b c := by
    obtain ⟨n,a⟩ := a
    obtain ⟨m,b⟩ := b
    obtain ⟨l,c⟩ := c
    apply Sigma.ext (Nat.add_assoc n m l)
    induction a using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h U =>
      induction b using gamma_named_iso_class_induction hc C Ξ hΞ with
      | h V =>
        induction c using gamma_named_iso_class_induction hc C Ξ hΞ with
        | h W =>
          change HEq (gammaNamedRVIsoMul hc C Ξ hΞ (gammaNamedRVIsoMul hc C Ξ hΞ
              (gammaNamedRVIsoClass hc C Ξ hΞ U) (gammaNamedRVIsoClass hc C Ξ hΞ V))
              (gammaNamedRVIsoClass hc C Ξ hΞ W))
            (gammaNamedRVIsoMul hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ U)
              (gammaNamedRVIsoMul hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ V)
                (gammaNamedRVIsoClass hc C Ξ hΞ W)))
          rw [gammaNamedRVIsoMul_class,gammaNamedRVIsoMul_class,gammaNamedRVIsoMul_class,
            gammaNamedRVIsoMul_class]
          exact gen_product_assoc hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ)
            (gammaNamedRVIsoClass_eq_of_iso' hc C Ξ hΞ) U V W

instance gammaNamedRVIsoClassesGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (GammaNamedRVIsoClasses hc C Ξ hΞ) where
  mul_zero {n m} a := by
    induction a using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h U =>
      rw [gammaNamedRVIso_mul_def,gammaNamedRVIso_zero_eq,gammaNamedRVIsoMul_class,gammaNamedRVIso_zero_eq]
      exact gen_product_right_zero hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ)
        (gammaNamedRVIsoClass_eq_of_iso' hc C Ξ hΞ) U
  zero_mul {n m} b := by
    induction b using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h V =>
      rw [gammaNamedRVIso_mul_def,gammaNamedRVIso_zero_eq,gammaNamedRVIsoMul_class,gammaNamedRVIso_zero_eq]
      exact gen_product_left_zero hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ)
        (gammaNamedRVIsoClass_eq_of_iso' hc C Ξ hΞ) V
  mul_add {n m} a b c := by
    induction a using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h U =>
      induction b using gamma_named_iso_class_induction hc C Ξ hΞ with
      | h V =>
        induction c using gamma_named_iso_class_induction hc C Ξ hΞ with
        | h W =>
          rw [gammaNamedRVIso_mul_def,gammaNamedRVIso_mul_def,gammaNamedRVIso_mul_def,
            ← gammaNamedRVIsoClass_coprod,gammaNamedRVIsoMul_class,gammaNamedRVIsoMul_class,
            gammaNamedRVIsoMul_class,← gammaNamedRVIsoClass_coprod]
          exact gen_product_right_distrib hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ)
            (gammaNamedRVIsoClass_eq_of_iso' hc C Ξ hΞ) U V W
  add_mul {n m} a b c := by
    induction a using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h U =>
      induction b using gamma_named_iso_class_induction hc C Ξ hΞ with
      | h V =>
        induction c using gamma_named_iso_class_induction hc C Ξ hΞ with
        | h W =>
          rw [gammaNamedRVIso_mul_def,gammaNamedRVIso_mul_def,gammaNamedRVIso_mul_def,
            ← gammaNamedRVIsoClass_coprod,gammaNamedRVIsoMul_class,gammaNamedRVIsoMul_class,
            gammaNamedRVIsoMul_class,← gammaNamedRVIsoClass_coprod]
          exact gen_product_left_distrib hc C Ξ hΞ (gammaNamedRVIsoClass hc C Ξ hΞ)
            (gammaNamedRVIsoClass_eq_of_iso' hc C Ξ hΞ) U V W

instance gammaNamedRVIsoClassesGSemiring : DirectSum.GSemiring (GammaNamedRVIsoClasses hc C Ξ hΞ) where
  natCast n :=
    letI := gammaNamedRVIsoClassesAddCommMonoid hc C Ξ hΞ 0
    (n • gammaNamedRVIsoClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ) : GammaNamedRVIsoClasses hc C Ξ hΞ 0)
  natCast_zero :=
    letI := gammaNamedRVIsoClassesAddCommMonoid hc C Ξ hΞ 0
    zero_nsmul _
  natCast_succ n := by
    letI := gammaNamedRVIsoClassesAddCommMonoid hc C Ξ hΞ 0
    simp only [succ_nsmul,one_nsmul]
    rfl

/-- The graded semiring of Gamma-named RV isomorphism classes. -/
abbrev GammaNamedRVIsoSemiring := DirectSum ℕ (GammaNamedRVIsoClasses hc C Ξ hΞ)

/-! ### Projection to blowup classes -/

def gammaNamedBlowupProjectionOn : (n : ℕ) → GammaNamedRVIsoClasses hc C Ξ hΞ n → GammaNamedRVClasses hc C Ξ hΞ n
  | 0 => id
  | _+1 => Quotient.lift (fun U => gammaVolumeBlowupClass hc 𝔇 𝔅 U)
      (fun U V ⟨e,he⟩ => gammaVolumeBlowupClass_iso hc 𝔇 𝔅 e he)

theorem gammaNamedBlowupProjectionOn_class {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedBlowupProjectionOn hc C Ξ hΞ n (gammaNamedRVIsoClass hc C Ξ hΞ U) =
      gammaNamedRVClass hc C Ξ hΞ U := by
  cases n <;> rfl

def gammaNamedBlowupProjectionAdd (n : ℕ) :
    GammaNamedRVIsoClasses hc C Ξ hΞ n →+ GammaNamedRVClasses hc C Ξ hΞ n where
  toFun := gammaNamedBlowupProjectionOn hc C Ξ hΞ n
  map_zero' := by
    rw [gammaNamedRVIso_zero_eq,gammaNamedBlowupProjectionOn_class,gammaNamedRV_zero_eq]
  map_add' a b := by
    induction a using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h U =>
      induction b using gamma_named_iso_class_induction hc C Ξ hΞ with
      | h V =>
        rw [← gammaNamedRVIsoClass_coprod,gammaNamedBlowupProjectionOn_class,
          gammaNamedBlowupProjectionOn_class,gammaNamedBlowupProjectionOn_class,gammaNamedRVClass_coprod]

theorem gammaNamedBlowupProjectionAdd_surjective (n : ℕ) :
    Function.Surjective (gammaNamedBlowupProjectionAdd hc C Ξ hΞ n) := by
  intro a
  obtain ⟨U,rfl⟩ := gammaNamedRVClass_surjective hc C Ξ hΞ n a
  exact ⟨gammaNamedRVIsoClass hc C Ξ hΞ U,gammaNamedBlowupProjectionOn_class hc C Ξ hΞ U⟩

/-- The graded projection from isomorphism classes to blowup classes. -/
def gammaNamedGradedBlowupProjection : GammaNamedRVIsoSemiring hc C Ξ hΞ →+* GammaNamedRVSemiring hc C Ξ hΞ := by
  let F (n : ℕ) := (DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) n).comp (gammaNamedBlowupProjectionAdd hc C Ξ hΞ n)
  apply DirectSum.toSemiring F
  · change DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) 0
      (gammaNamedBlowupProjectionOn hc C Ξ hΞ 0 (gammaNamedRVIsoClass hc C Ξ hΞ (gammaUnit hc C Ξ hΞ))) = 1
    rw [gammaNamedBlowupProjectionOn_class]
    rfl
  · intro n m a b
    induction a using gamma_named_iso_class_induction hc C Ξ hΞ with
    | h U =>
      induction b using gamma_named_iso_class_induction hc C Ξ hΞ with
      | h V =>
        change DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) (n+m)
          (gammaNamedBlowupProjectionOn hc C Ξ hΞ (n+m) (gammaNamedRVIsoMul hc C Ξ hΞ
            (gammaNamedRVIsoClass hc C Ξ hΞ U) (gammaNamedRVIsoClass hc C Ξ hΞ V))) =
          DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) n (gammaNamedBlowupProjectionOn hc C Ξ hΞ n
            (gammaNamedRVIsoClass hc C Ξ hΞ U)) *
          DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) m (gammaNamedBlowupProjectionOn hc C Ξ hΞ m
            (gammaNamedRVIsoClass hc C Ξ hΞ V))
        rw [DirectSum.of_mul_of,gammaNamedRVIsoMul_class,gammaNamedBlowupProjectionOn_class,
          gammaNamedBlowupProjectionOn_class,gammaNamedBlowupProjectionOn_class]
        exact congrArg (DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) (n+m))
          (gammaNamedRVMul_class hc C Ξ hΞ U V).symm

theorem gammaNamedGradedBlowupProjection_of (n : ℕ) (a : GammaNamedRVIsoClasses hc C Ξ hΞ n) :
    gammaNamedGradedBlowupProjection hc C Ξ hΞ (DirectSum.of (GammaNamedRVIsoClasses hc C Ξ hΞ) n a) =
      DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) n (gammaNamedBlowupProjectionAdd hc C Ξ hΞ n a) := by
  change DirectSum.toAddMonoid
    (fun i => (DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) i).comp (gammaNamedBlowupProjectionAdd hc C Ξ hΞ i))
    (DirectSum.of (GammaNamedRVIsoClasses hc C Ξ hΞ) n a) = _
  exact DirectSum.toAddMonoid_of _ n a

theorem gammaNamedGradedBlowupProjection_surjective :
    Function.Surjective (gammaNamedGradedBlowupProjection hc C Ξ hΞ) := by
  intro a
  induction a using DirectSum.induction_on with
  | zero => exact ⟨0,map_zero _⟩
  | of n a =>
    obtain ⟨b,hb⟩ := gammaNamedBlowupProjectionAdd_surjective hc C Ξ hΞ n a
    exact ⟨DirectSum.of (GammaNamedRVIsoClasses hc C Ξ hΞ) n b,
      (gammaNamedGradedBlowupProjection_of hc C Ξ hΞ n b).trans (congrArg _ hb)⟩
  | add a b ha hb =>
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    exact ⟨x+y,(map_add _ x y).trans (congrArg₂ (fun x y => x+y) hx hy)⟩

end IntegrationInACVF.Section7.HK
