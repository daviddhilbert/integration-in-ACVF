import Integration7.ElementaryBlowupConstruction
import Integration7.ScalarRVMaps

/-! The nonzero part of the actual blowup cone. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {P Q : Space LRV M} {A : DefSet P S} {B : DefSet Q S}

def nonzeroBlowupConeSet (S : Set M) : DefSet (rawRVSpace (M := M) 1) S :=
  (blowupConeSet S).sdiff (zeroLabelsAt S (0 : Fin 1))

theorem mem_nonzeroBlowupConeSet (S : Set M) (t : Fin 1 → CanonicalRV.RVSort M) :
    t ∈ (nonzeroBlowupConeSet (M := M) S).carrier ↔
      RVOperations.absoluteHom (t 0) < 1 ∧ t 0 ≠ 0 := by
  constructor
  · intro h
    exact ⟨(mem_blowupConeSet S t).mp h.1, (rv_nonzero_iff_raw _).mpr h.2⟩
  · rintro ⟨h, h0⟩
    exact ⟨(mem_blowupConeSet S t).mpr h, (rv_nonzero_iff_raw _).mp h0⟩

theorem nonzeroBlowupConeSet_subset (S : Set M) :
    (nonzeroBlowupConeSet (M := M) S).carrier ⊆ (blowupConeSet S).carrier :=
  Set.diff_subset

theorem rv_ne_zero_of_absolute_one (c : CanonicalRV.RVSort M)
    (h : RVOperations.absoluteHom c = 1) : c ≠ 0 := by
  intro hc
  rw [hc, map_zero] at h
  exact zero_ne_one h

def nonzeroConeFibreMap (F : Map A B)
    (c : Map A (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hc : ∀ a, RVOperations.absoluteHom ((c a).val 0) = 1) :
    Map (A.prod (nonzeroBlowupConeSet S)) (B.prod (nonzeroBlowupConeSet S)) := by
  let π := Map.prodFst A (nonzeroBlowupConeSet S)
  let σ := Map.prodSnd A (nonzeroBlowupConeSet S)
  let m := (rvMultiply S).comp (((c.comp π).pair σ.toUniv).toUniv)
  let mc : Map (A.prod (nonzeroBlowupConeSet S)) (nonzeroBlowupConeSet S) :=
    m.corestrict (by
      intro p
      apply (mem_nonzeroBlowupConeSet S _).mpr
      have hs := (mem_nonzeroBlowupConeSet S _).mp p.property.2
      change RVOperations.absoluteHom ((c (π p)).val 0 * p.val.2 0) < 1 ∧
        (c (π p)).val 0 * p.val.2 0 ≠ 0
      constructor
      · rw [map_mul, hc, one_mul]
        exact hs.1
      · exact mul_ne_zero (rv_ne_zero_of_absolute_one _ (hc _)) hs.2)
  exact (F.comp π).pair mc

@[simp] theorem nonzeroConeFibreMap_value (F : Map A B)
    (c : Map A (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hc : ∀ a, RVOperations.absoluteHom ((c a).val 0) = 1)
    (p : A.prod (nonzeroBlowupConeSet S)) :
    (nonzeroConeFibreMap F c hc p).val =
      ((F (Map.prodFst _ _ p)).val, fun _ => (c (Map.prodFst _ _ p)).val 0 * p.val.2 0) := rfl

theorem nonzeroConeFibreMap_bijective (F : Map A B) (hF : Function.Bijective F)
    (c : Map A (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hc : ∀ a, RVOperations.absoluteHom ((c a).val 0) = 1) :
    Function.Bijective (nonzeroConeFibreMap F c hc) := by
  constructor
  · intro p q he
    have ha : Map.prodFst _ _ p = Map.prodFst _ _ q :=
      hF.1 (Subtype.ext (congrArg
        (fun z : B.prod (nonzeroBlowupConeSet S) => z.val.1) he))
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ha
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have hm := congrArg (fun z : B.prod (nonzeroBlowupConeSet S) => z.val.2 0) he
      change (c (Map.prodFst _ _ p)).val 0 * p.val.2 0 =
        (c (Map.prodFst _ _ q)).val 0 * q.val.2 0 at hm
      rw [ha] at hm
      exact mul_left_cancel₀ (rv_ne_zero_of_absolute_one _ (hc _)) hm
  · intro q
    obtain ⟨a, ha⟩ := hF.2 ⟨q.val.1, q.property.1⟩
    have hc0 := rv_ne_zero_of_absolute_one _ (hc a)
    let s : Fin 1 → CanonicalRV.RVSort M := fun _ => ((c a).val 0)⁻¹ * q.val.2 0
    have hs : s ∈ (nonzeroBlowupConeSet S).carrier := by
      apply (mem_nonzeroBlowupConeSet S s).mpr
      have hq := (mem_nonzeroBlowupConeSet S _).mp q.property.2
      constructor
      · change RVOperations.absoluteHom (((c a).val 0)⁻¹ * q.val.2 0) < 1
        rw [map_mul, map_inv₀, hc, inv_one, one_mul]
        exact hq.1
      · exact mul_ne_zero (inv_ne_zero hc0) hq.2
    refine ⟨⟨(a.val, s), a.property, hs⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ha
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change (c a).val 0 * (((c a).val 0)⁻¹ * q.val.2 0) = q.val.2 0
      exact mul_inv_cancel_left₀ hc0 _

end IntegrationInACVF.Section7
