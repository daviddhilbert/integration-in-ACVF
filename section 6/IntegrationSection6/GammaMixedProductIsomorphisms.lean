import IntegrationSection6.GammaMixedProducts
import Section5.GammaLift
import IntegrationSection5.CoordinateFibreMaps

/-! Definable insertion and projection of a VF prefix with a frozen tail. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n p m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def mixedProductPack {a b : ℕ} (p : Point (M := M) n m) (q : Point (M := M) a b) :
    Point (M := M) (n+a) (m+b) := (Fin.append p.1 q.1,Fin.append p.2 q.2)

@[simp] theorem mixedProductLeft_pack {a b : ℕ} (p : Point (M := M) n m) (q : Point (M := M) a b) :
    mixedProductLeft (mixedProductPack p q) = p := by
  apply Prod.ext <;> apply funext <;> intro i <;> exact Fin.append_left _ _ i

@[simp] theorem mixedProductRight_pack {a b : ℕ} (p : Point (M := M) n m) (q : Point (M := M) a b) :
    mixedProductRight (mixedProductPack p q) = q := by
  apply Prod.ext <;> apply funext <;> intro i <;> exact Fin.append_right _ _ i

theorem mixedProductPack_split {a b : ℕ} (p : Point (M := M) (n+a) (m+b)) :
    mixedProductPack (mixedProductLeft p) (mixedProductRight p) = p :=
  Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd

def mixedProductEquiv {a b : ℕ} (A : Set (Point (M := M) n m)) (C : Set (Point (M := M) a b)) :
    mixedProductSet A C ≃ A × C where
  toFun p := (⟨mixedProductLeft p.val,p.property.1⟩,⟨mixedProductRight p.val,p.property.2⟩)
  invFun p := ⟨mixedProductPack p.1.val p.2.val,by
    change mixedProductLeft _ ∈ A ∧ mixedProductRight _ ∈ C
    simpa only [mixedProductLeft_pack,mixedProductRight_pack] using And.intro p.1.property p.2.property⟩
  left_inv p := Subtype.ext (mixedProductPack_split p.val)
  right_inv p := Prod.ext (Subtype.ext (mixedProductLeft_pack _ _)) (Subtype.ext (mixedProductRight_pack _ _))

variable {B : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {a b u v c d : ℕ}
variable {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) a b)}
variable {D : Set (Point (M := M) u v)} {E : Set (Point (M := M) c d)}

def gammaMixedProductIso (e : GammaIso B A D) (f : GammaIso B C E) :
    GammaIso B (mixedProductSet A C) (mixedProductSet D E) := by
  let eqv := ((mixedProductEquiv A C).trans (Equiv.prodCongr e.equiv f.equiv)).trans (mixedProductEquiv D E).symm
  refine ⟨eqv,?_⟩
  have h : GammaGraphDefinable B (fun p q =>
      (∃ x : A, x.val = mixedProductLeft p ∧ (e.equiv x).val = mixedProductLeft q) ∧
      (∃ y : C, y.val = mixedProductRight p ∧ (f.equiv y).val = mixedProductRight q)) :=
    (e.graph.preimage_maps (mixedCoordinatePointMap (Fin.castAdd a) (Fin.castAdd b) B.real)
      (mixedCoordinatePointMap (Fin.castAdd c) (Fin.castAdd d) B.real)).inter
    (f.graph.preimage_maps (mixedCoordinatePointMap (Fin.natAdd n) (Fin.natAdd m) B.real)
      (mixedCoordinatePointMap (Fin.natAdd u) (Fin.natAdd v) B.real))
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨⟨x,hx,hq⟩,⟨y,hy,hr⟩⟩
    have hp : mixedProductPack x.val y.val = p := by rw [hx,hy]; exact mixedProductPack_split p
    let z : mixedProductSet A C := (mixedProductEquiv A C).symm (x,y)
    refine ⟨z,hp,?_⟩
    have hz : mixedProductEquiv A C z = (x,y) := (mixedProductEquiv A C).apply_symm_apply (x,y)
    change ((mixedProductEquiv D E).symm ((Equiv.prodCongr e.equiv f.equiv) (mixedProductEquiv A C z))).val = q
    rw [hz]
    change mixedProductPack (e.equiv x).val (f.equiv y).val = q
    rw [hq,hr]
    exact mixedProductPack_split q
  · rintro ⟨z,hz,hq⟩
    let x := (mixedProductEquiv A C z).1
    let y := (mixedProductEquiv A C z).2
    refine ⟨⟨x,congrArg mixedProductLeft hz,?_⟩,⟨y,congrArg mixedProductRight hz,?_⟩⟩
    · exact (mixedProductLeft_pack (e.equiv x).val (f.equiv y).val).symm.trans (congrArg mixedProductLeft hq)
    · exact (mixedProductRight_pack (e.equiv x).val (f.equiv y).val).symm.trans (congrArg mixedProductRight hq)

end IntegrationInACVF.Section6
