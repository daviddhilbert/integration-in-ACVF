import IntegrationSection4.Cells

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.ScalarPositioning

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def vfSet (D : Set M) : Set (VF (M := M)) := {x | x.val ∈ D}

theorem raw_vfSet (D : Set M) (hDVF : D ⊆ {x | iVF x}) : Cells.rawSet (vfSet D) = D := by
  ext x
  exact ⟨fun ⟨y,hy,he⟩ => he ▸ hy,fun hx => ⟨⟨x,hDVF hx⟩,hx,rfl⟩⟩

def lift (D : Set M) (f : M → M) (hfVF : ∀ x ∈ D, iVF (f x)) (x : VF (M := M)) : VF (M := M) :=
  if h : x.val ∈ D then ⟨f x.val,hfVF _ h⟩ else 0

theorem lift_on (D : Set M) (f : M → M) (hfVF : ∀ x ∈ D, iVF (f x))
    (x : VF (M := M)) (hx : x.val ∈ D) : (lift D f hfVF x).val = f x.val := by
  rw [lift,dif_pos hx]

theorem raw_lift_on (D : Set M) (hDVF : D ⊆ {x | iVF x})
    (f : M → M) (hfVF : ∀ x ∈ D, iVF (f x)) (x : M) (hx : x ∈ D) :
    Cells.rawMap (lift D f hfVF) x = f x := by
  have hh := Cells.rawMap_on (lift D f hfVF) (⟨x,hDVF hx⟩ : VF (M := M))
  exact hh.trans (lift_on D f hfVF _ hx)

theorem image_congr {A : Set M} {f g : M → M} (he : ∀ x ∈ A, f x = g x)
    (D : Set M) (hDA : D ⊆ A) : f '' D = g '' D := by
  ext y
  exact ⟨fun ⟨x,hx,hy⟩ => ⟨x,hx,(he x (hDA hx)).symm.trans hy⟩,
    fun ⟨x,hx,hy⟩ => ⟨x,hx,(he x (hDA hx)).trans hy⟩⟩

theorem open_congr {A : Set M} {f g : M → M} (he : ∀ x ∈ A, f x = g x)
    (hOO : MaximalOpenClasses.OpenToOpen A f) : MaximalOpenClasses.OpenToOpen A g := by
  intro D hDA
  rw [← image_congr he D hDA]
  exact hOO D hDA

theorem linear_congr {A : Set M} {f g : M → M} (hfVF : ∀ x ∈ A, iVF (f x))
    (hgVF : ∀ x ∈ A, iVF (g x)) (he : ∀ x ∈ A, f x = g x)
    (s : Values.Gamma (M := M)) (hLin : GammaLinearity.GammaLinear A f hfVF s) :
    GammaLinearity.GammaLinear A g hgVF s := by
  intro x y hx hy
  have hfx : (⟨f x.val,hfVF _ hx⟩ : VFType (M := M)) = ⟨g x.val,hgVF _ hx⟩ := Subtype.ext (he _ hx)
  have hfy : (⟨f y.val,hfVF _ hy⟩ : VFType (M := M)) = ⟨g y.val,hgVF _ hy⟩ := Subtype.ext (he _ hy)
  have hh := hLin x y hx hy
  change Values.vfValueHom ((_ : VFType (M := M))-(_ : VFType (M := M))) = _ at hh ⊢
  rwa [hfx,hfy] at hh

theorem bijective (D E : Set M) (hDVF : D ⊆ {x | iVF x})
    (f : M → M) (hfVF : ∀ x ∈ D, iVF (f x)) (hbij : Set.BijOn f D E) :
    Set.BijOn (lift D f hfVF) (vfSet D) (vfSet E) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    change (lift D f hfVF x).val ∈ E
    rw [lift_on D f hfVF x hx]
    exact hbij.1 hx
  · intro x hx y hy he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    rw [lift_on D f hfVF x hx,lift_on D f hfVF y hy] at hh
    exact hbij.2.1 hx hy hh
  · intro y hy
    obtain ⟨x,hx,hfx⟩ := hbij.2.2 hy
    refine ⟨⟨x,hDVF hx⟩,hx,Subtype.ext ?_⟩
    exact (lift_on D f hfVF _ hx).trans hfx

theorem raw_image (D : Set M) (hDVF : D ⊆ {x | iVF x})
    (f : M → M) (hfVF : ∀ x ∈ D, iVF (f x)) :
    Cells.rawSet (lift D f hfVF '' vfSet D) = f '' D := by
  ext y
  constructor
  · rintro ⟨z,⟨x,hx,rfl⟩,he⟩
    exact ⟨x.val,hx,(lift_on D f hfVF x hx).symm.trans he⟩
  · rintro ⟨x,hx,rfl⟩
    let X : VF (M := M) := ⟨x,hDVF hx⟩
    exact ⟨lift D f hfVF X,⟨X,hx,rfl⟩,lift_on D f hfVF X hx⟩

theorem raw_image_of_agrees (D : Set M) (hDVF : D ⊆ {x | iVF x})
    (f : M → M) (φ : VF (M := M) → VF (M := M))
    (hφ : ∀ x ∈ D, Cells.rawMap φ x = f x) :
    Cells.rawSet (φ '' vfSet D) = f '' D := by
  have hp (x : VF (M := M)) (hx : x.val ∈ D) : (φ x).val = f x.val :=
    (Cells.rawMap_on φ x).symm.trans (hφ x.val hx)
  ext y
  constructor
  · rintro ⟨z,⟨x,hx,rfl⟩,he⟩
    exact ⟨x.val,hx,(hp x hx).symm.trans he⟩
  · rintro ⟨x,hx,rfl⟩
    let X : VF (M := M) := ⟨x,hDVF hx⟩
    exact ⟨φ X,⟨X,hx,rfl⟩,hp X hx⟩

end IntegrationInACVF.Section4.ScalarPositioning
