import IntegrationSection6.Blowups
import Section4.MapParameters

/-! The additional-real-parameter convention in Definition 6.7, preserving
all actual locus data and the exact number of forward blowups. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S T : Set M} {k : ℕ}

def extendObject (hST : S ⊆ T) (U : RVObject (M := M) S k) : RVObject (M := M) T k where
  arity := U.arity
  domain := U.domain.extend hST
  volume := U.volume.extend hST

def extendHom (hST : S ⊆ T) {U V : RVObject (M := M) S k} (f : RVHom U V) :
    RVHom (extendObject hST U) (extendObject hST V) where
  map := f.map.extend hST
  volumetric := f.volumetric
  finite_volume_images := f.finite_volume_images

def extendIso (hST : S ⊆ T) {U V : RVObject (M := M) S k} (e : U ≅ V) :
    extendObject hST U ≅ extendObject hST V where
  hom := extendHom hST e.hom
  inv := extendHom hST e.inv
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro a
    exact iso_hom_inv_apply e a
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro a
    exact iso_inv_hom_apply e a

theorem Admissible.extend (hST : S ⊆ T) {U : RVObject (M := M) S k}
    {i : Fin k} (h : Admissible U i) : Admissible (extendObject hST U) i where
  nonzero := h.nonzero
  algebraic a := (h.algebraic a).mono (by
    rintro x (hx | hx)
    · exact Or.inl (hST hx)
    · exact Or.inr hx)

def Blowup.extend (hST : S ⊆ T) {U V : RVObject (M := M) S k}
    (h : Blowup U V) : Blowup (extendObject hST U) (extendObject hST V) where
  center := extendObject hST h.center
  coordinate := h.coordinate
  admissible := h.admissible.extend hST
  locus := h.locus.extend hST
  contained := h.contained
  chart := extendIso hST h.chart
  result := extendIso hST h.result

theorem IteratedBlowup.extend (hST : S ⊆ T) {U V : RVObject (M := M) S k}
    {n : ℕ} (h : IteratedBlowup n U V) :
    IteratedBlowup n (extendObject hST U) (extendObject hST V) := by
  induction h with
  | zero he => exact .zero (he.map (extendIso hST))
  | cons h _ ih => exact .cons (h.extend hST) ih

theorem Isp.extend (hST : S ⊆ T) {U V : RVObject (M := M) S k} (h : Isp U V) :
    Isp (extendObject hST U) (extendObject hST V) := by
  obtain ⟨m,n,A,B,hu,hv,he⟩ := h
  exact ⟨m,n,extendObject hST A,extendObject hST B,hu.extend hST,hv.extend hST,
    he.map (extendIso hST)⟩

end IntegrationInACVF.Section6
