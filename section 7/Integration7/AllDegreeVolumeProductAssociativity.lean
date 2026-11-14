import Integration7.AllDegreeVolumeData
import Integration7.AllDegreeVolumeProductIsomorphisms

/-! Reassociation for the original product in every volume degree.
The density proof is multiplication associativity, including ordinary RV[0]. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] rvVolumeProductData rvFiniteProductObject rvProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeProductAssocIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m l : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n)
    (V : RVVolumeObject (M := M) (C.base : Set M) m)
    (W : RVVolumeObject (M := M) (C.base : Set M) l) :
    RVVolumeIsoInDegree (C.base : Set M) ((n+m)+l)
      (rvVolumeProduct _ (n+m) l (rvVolumeProduct _ n m U V) W)
      ((Nat.add_assoc n m l).symm ▸ rvVolumeProduct _ n (m+l) U (rvVolumeProduct _ m l V W)) := by
  let A := rvVolumeUnderlying (C.base : Set M) n U
  let B := rvVolumeUnderlying (C.base : Set M) m V
  let L := rvVolumeUnderlying (C.base : Set M) l W
  let D := rvVolumeProductData (n+m) l (rvVolumeProduct (C.base : Set M) n m U V) W
  let E := rvVolumeProductData n (m+l) U (rvVolumeProduct (C.base : Set M) m l V W)
  let ωU := rvVolumeForm (C.base : Set M) n U
  let ωV := rvVolumeForm (C.base : Set M) m V
  let ωW := rvVolumeForm (C.base : Set M) l W
  have hUV (u : A.obj.domain) (v : B.obj.domain) := rvVolumeProduct_density_pair n m U V u v
  have hVW (v : B.obj.domain) (w : L.obj.domain) := rvVolumeProduct_density_pair m l V W v w
  have hD (uv : (rvVolumeUnderlying (C.base : Set M) (n+m)
      (rvVolumeProduct (C.base : Set M) n m U V)).obj.domain) (w : L.obj.domain) :=
    rvVolumeProductData_density_pair (n+m) l (rvVolumeProduct (C.base : Set M) n m U V) W uv w
  have hE (u : A.obj.domain) (vw : (rvVolumeUnderlying (C.base : Set M) (m+l)
      (rvVolumeProduct (C.base : Set M) m l V W)).obj.domain) :=
    rvVolumeProductData_density_pair n (m+l) U (rvVolumeProduct (C.base : Set M) m l V W) u vw
  let hdegree := Nat.add_assoc n m l
  rw [← rvVolumeProductData_toObject (n+m) l (rvVolumeProduct (C.base : Set M) n m U V) W,
    ← rvVolumeProductData_toObject n (m+l) U (rvVolumeProduct (C.base : Set M) m l V W)]
  change RVVolumeIsoInDegree (C.base : Set M) ((n+m)+l) D.toObject (hdegree.symm ▸ E.toObject)
  cases n <;> cases m <;> cases l
  all_goals
    apply rvVolumeDataReindexedIso hc C hdegree D E
      (rvProductAssocMap A.obj B.obj L.obj) (rvProductAssocMap_bijective A.obj B.obj L.obj)
    · intro x
      obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (rvProductObject A.obj B.obj).domain L.obj.domain x
      obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain B.obj.domain uv
      change (rvProductObject A.obj (rvProductObject B.obj L.obj)).value
        (rvProductAssocMap A.obj B.obj L.obj
          (rvPackPair (rvProductObject A.obj B.obj).domain L.obj.domain
            (rvPackPair A.obj.domain B.obj.domain u v) w)) ∘ finCongr hdegree =
          (rvProductObject (rvProductObject A.obj B.obj) L.obj).value
            (rvPackPair (rvProductObject A.obj B.obj).domain L.obj.domain
              (rvPackPair A.obj.domain B.obj.domain u v) w)
      rw [rvProductAssocMap_pair,rvProductObject_value_pair,rvProductObject_value_pair,
        rvProductObject_value_pair,rvProductObject_value_pair]
      exact (Fin.append_assoc (A.obj.value u) (B.obj.value v) (L.obj.value w)).symm
    · intro x
      obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (rvProductObject A.obj B.obj).domain L.obj.domain x
      obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain B.obj.domain uv
      apply (congrArg E.form.value (rvProductAssocMap_pair A.obj B.obj L.obj u v w)).trans
      exact (hE u (rvPackPair B.obj.domain L.obj.domain v w)).trans
        ((congrArg (fun t => ωU.value u * t) (hVW v w)).trans
          ((mul_assoc (ωU.value u) (ωV.value v) (ωW.value w)).symm.trans
            ((congrArg (fun t => t * ωW.value w) (hUV u v)).symm.trans
              (hD (rvPackPair A.obj.domain B.obj.domain u v) w).symm)))

end IntegrationInACVF.Section7
