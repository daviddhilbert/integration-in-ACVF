import Integration7.HKVolumeCoproducts
import Integration7.HKRVProductIsomorphisms

/-! Reassociation for the original product in every volume degree.
The density proof is multiplication associativity, including weighted measured RV[0]. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK

set_option allowUnsafeReducibility true in
attribute [local reducible] productData rvFiniteProductObject rvProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def productAssocIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m l : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n)
    (V : RVVolumeObject (M := M) (C.base : Set M) m)
    (W : RVVolumeObject (M := M) (C.base : Set M) l) :
    rvVolumeIsoInDegree (C.base : Set M) ((n+m)+l)
      (product _ (n+m) l (product _ n m U V) W)
      ((Nat.add_assoc n m l).symm ▸ product _ n (m+l) U (product _ m l V W)) := by
  let A := underlying (C.base : Set M) n U
  let B := underlying (C.base : Set M) m V
  let L := underlying (C.base : Set M) l W
  let D := productData (n+m) l (product (C.base : Set M) n m U V) W
  let E := productData n (m+l) U (product (C.base : Set M) m l V W)
  let ωU := form (C.base : Set M) n U
  let ωV := form (C.base : Set M) m V
  let ωW := form (C.base : Set M) l W
  have hUV (u : A.obj.domain) (v : B.obj.domain) := product_density_pair n m U V u v
  have hVW (v : B.obj.domain) (w : L.obj.domain) := product_density_pair m l V W v w
  have hD (uv : (underlying (C.base : Set M) (n+m)
      (product (C.base : Set M) n m U V)).obj.domain) (w : L.obj.domain) :=
    productData_density_pair (n+m) l (product (C.base : Set M) n m U V) W uv w
  have hE (u : A.obj.domain) (vw : (underlying (C.base : Set M) (m+l)
      (product (C.base : Set M) m l V W)).obj.domain) :=
    productData_density_pair n (m+l) U (product (C.base : Set M) m l V W) u vw
  let hdegree := Nat.add_assoc n m l
  rw [← productData_ofData (n+m) l (product (C.base : Set M) n m U V) W,
    ← productData_ofData n (m+l) U (product (C.base : Set M) m l V W)]
  change rvVolumeIsoInDegree (C.base : Set M) ((n+m)+l) (ofData D) (hdegree.symm ▸ (ofData E))
  cases n <;> cases m <;> cases l
  all_goals
    apply dataReindexedIso hc C hdegree D E
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

end IntegrationInACVF.Section7.HK
