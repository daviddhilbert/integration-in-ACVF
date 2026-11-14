import Integration7.GradedVolumeBlowupProjection

/-! Lemma 7.4: common forward blowups define a congruence in every
degree, compatible with actual coproduct addition and the graded product. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem lemma_7_4 (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    (∀ n, Equivalence (MuIsp (C.base : Set M) n)) ∧
    (∀ n (U U' V V' : RVVolumeObject (M := M) (C.base : Set M) n),
      MuIsp (C.base : Set M) n U U' → MuIsp (C.base : Set M) n V V' →
        MuIsp (C.base : Set M) n (rvVolumeCoprod _ n U V) (rvVolumeCoprod _ n U' V')) ∧
    (∀ n m (U U' : RVVolumeObject (M := M) (C.base : Set M) n)
      (V V' : RVVolumeObject (M := M) (C.base : Set M) m),
      MuIsp (C.base : Set M) n U U' → MuIsp (C.base : Set M) m V V' →
        MuIsp (C.base : Set M) (n+m) (rvVolumeProduct _ n m U V) (rvVolumeProduct _ n m U' V')) :=
  ⟨fun n => (muIspSetoid hc C n).iseqv,
    fun n U U' V V' h g => muIsp_coprod hc C (n := n) (U := U) (U' := U') (V := V) (V' := V') h g,
    fun n m U U' V V' h g => muIsp_product hc C (n := n) (m := m)
      (U := U) (U' := U') (V := V) (V' := V') h g⟩

end IntegrationInACVF.Section7
