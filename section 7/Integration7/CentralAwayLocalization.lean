import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Group.Units.Hom

/-! Localization at a central element in a possibly noncommutative ring,
including its universal property. Zero divisors are permitted. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v
variable {R : Type u} [Ring R] (l : R) [hl : Fact (∀ x : R, Commute x l)]

instance centralPowersOreSet : OreLocalization.OreSet (Submonoid.powers l) where
  ore_right_cancel a b s h := by
    obtain ⟨n,hn⟩ := s.property
    have ha : Commute a (s : R) := hn ▸ (hl.out a).pow_right n
    have hb : Commute b (s : R) := hn ▸ (hl.out b).pow_right n
    exact ⟨s,ha.eq.symm.trans (h.trans hb.eq)⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq r s := by
    obtain ⟨n,hn⟩ := s.property
    have h : Commute r (s : R) := hn ▸ (hl.out r).pow_right n
    exact h.eq.symm

abbrev CentralAway := OreLocalization (Submonoid.powers l) R

def centralAwayMap : R →+* CentralAway l := OreLocalization.numeratorRingHom

theorem centralAwayMap_point_isUnit : IsUnit (centralAwayMap l l) :=
  OreLocalization.numerator_isUnit (⟨l,⟨1,pow_one l⟩⟩ : Submonoid.powers l)

variable {T : Type v} [Ring T]

def centralAwayLift (f : R →+* T) (hf : IsUnit (f l)) : CentralAway l →+* T := by
  let g : Submonoid.powers l →* T := f.toMonoidHom.comp (Submonoid.powers l).subtype
  have hg (s : Submonoid.powers l) : IsUnit (g s) := by
    obtain ⟨n,hn⟩ := s.property
    change IsUnit (f s.val)
    rw [← hn,map_pow]
    exact hf.pow n
  exact OreLocalization.universalHom f (IsUnit.liftRight g hg) (fun s => rfl)

@[simp] theorem centralAwayLift_map (f : R →+* T) (hf : IsUnit (f l)) (r : R) :
    centralAwayLift l f hf (centralAwayMap l r) = f r :=
  OreLocalization.universalHom_commutes _ _ _

theorem centralAwayLift_unique (f : R →+* T) (hf : IsUnit (f l))
    (g : CentralAway l →+* T) (hg : ∀ r, g (centralAwayMap l r) = f r) :
    g = centralAwayLift l f hf := OreLocalization.universalHom_unique _ _ _ g hg
end IntegrationInACVF.Section7
