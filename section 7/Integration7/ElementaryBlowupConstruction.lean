import Integration7.RVVolumeObjects
import Integration7.RVNonzero
import IntegrationSection6.ElementaryBlowup
import Section4.RVProductSymmetry

/-! Definition 7.1 in concrete last-coordinate charts. The underlying
admissibility and finite-volume construction are reused from Section 6;
the density is pulled back from the source object. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

structure BlowupAdmissible (U : PositiveRVVolumeObject (M := M) S k) : Prop where
  nonzero : ∀ u : U.underlying.obj.domain, U.underlying.obj.value u (Fin.last k) ≠ 0
  algebraic : ∀ u : U.underlying.obj.domain,
    AlgebraicAt (Section6.coordinateBase S (Fin.last k) (U.underlying.obj.value u))
      .rv (U.underlying.obj.value u (Fin.last k)).val

theorem BlowupAdmissible.toOrdinary {U : PositiveRVVolumeObject (M := M) S k}
    (h : BlowupAdmissible U) : Section6.Admissible U.underlying.obj (Fin.last k) where
  nonzero u := (rv_nonzero_iff_raw _).mp (h.nonzero u)
  algebraic := h.algebraic

abbrev blowupConeSet (S : Set M) : DefSet (rawRVSpace (M := M) 1) S :=
  Section6.positiveRV S

theorem mem_blowupConeSet (S : Set M) (t : Fin 1 → CanonicalRV.RVSort M) :
    t ∈ (blowupConeSet (M := M) S).carrier ↔ RVOperations.absoluteHom (t 0) < 1 :=
  Section6.positiveRV_iff_absolute_lt_one t

def blowupCoordinates (t : Fin (k + 1) → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) : Fin (k + 1) → CanonicalRV.RVSort M :=
  Section6.blowupValue (Fin.last k) t s

@[simp] theorem blowupCoordinates_head (t : Fin (k + 1) → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) (i : Fin k) :
    blowupCoordinates t s i.castSucc = t i.castSucc :=
  Section6.blowupValue_other _ _ _ _ (Fin.castSucc_ne_last i)

@[simp] theorem blowupCoordinates_last (t : Fin (k + 1) → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) : blowupCoordinates t s (Fin.last k) = s * t (Fin.last k) :=
  Section6.blowupValue_same _ _ _

structure ElementaryBlowup (U W : PositiveRVVolumeObject (M := M) S k) where
  admissible : BlowupAdmissible U
  chartMap : Map W.underlying.obj.domain (U.underlying.obj.domain.prod (blowupConeSet S))
  chartMap_bijective : Function.Bijective chartMap
  head : ∀ w (i : Fin k), W.underlying.obj.value w i.castSucc =
    U.underlying.obj.value (Map.prodFst _ _ (chartMap w)) i.castSucc
  last : ∀ w, W.underlying.obj.value w (Fin.last k) =
    (chartMap w).val.2 0 * U.underlying.obj.value (Map.prodFst _ _ (chartMap w)) (Fin.last k)
  volume : ∀ w, W.form.value w = U.form.value (Map.prodFst _ _ (chartMap w))

namespace ElementaryBlowup

variable {U W : PositiveRVVolumeObject (M := M) S k} (b : ElementaryBlowup U W)

def projection : Map W.underlying.obj.domain U.underlying.obj.domain :=
  (Map.prodFst _ _).comp b.chartMap

def parameter : Map W.underlying.obj.domain (blowupConeSet S) :=
  (Map.prodSnd _ _).comp b.chartMap

theorem parameter_mem (w : W.underlying.obj.domain) :
    RVOperations.absoluteHom ((b.parameter w).val 0) < 1 :=
  (mem_blowupConeSet S _).mp (b.parameter w).property

theorem last_eq_zero_iff (w : W.underlying.obj.domain) :
    W.underlying.obj.value w (Fin.last k) = 0 ↔ (b.parameter w).val 0 = 0 := by
  rw [b.last, mul_eq_zero]
  change ((b.parameter w).val 0 = 0 ∨
    U.underlying.obj.value (b.projection w) (Fin.last k) = 0) ↔ _
  exact or_iff_left (b.admissible.nonzero (b.projection w))

end ElementaryBlowup

def elementaryVolumeObject (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (h : BlowupAdmissible U) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) k where
  underlying := ⟨Section6.elementary U.underlying.obj (Fin.last k),
    Section6.elementary_finite_volume C.uncountable.le C.saturated C.small
      U.underlying.obj (Fin.last k) h.toOrdinary U.underlying.property⟩
  form := U.form.pullback (Section6.elementaryProjection U.underlying.obj (Fin.last k))

def elementaryVolumeBlowup (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (h : BlowupAdmissible U) :
    ElementaryBlowup U (elementaryVolumeObject C U h) where
  admissible := h
  chartMap := rvUnpack U.underlying.obj.domain (blowupConeSet (C.base : Set M))
  chartMap_bijective := rvUnpack_bijective _ _
  head w i := Section6.blowupValue_other _ _ _ _ (Fin.castSucc_ne_last i)
  last w := Section6.blowupValue_same _ _ _
  volume _ := rfl

end IntegrationInACVF.Section7
