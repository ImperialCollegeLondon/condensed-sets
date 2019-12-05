import category_theory.limits.limits
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal
import data.fintype

variable (α : Type*)

open category_theory

namespace category_theory.limits
namespace is_limit
universes v u

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

open_locale classical

#check limits.has_limit
#check category_theory.functor

instance finite_prod_of_binary_prod [has_binary_products.{v} C] [has_terminal.{v} C ] :
  has_finite_products.{v} C :=
⟨begin
  intros J fJ dJ,
  resetI,
  suffices : ∀ n : ℕ, fintype.card J = n → limits.has_limits_of_shape (discrete J) C,
    apply this (fintype.card J), refl,
  intro n, apply nat.rec_on n,
  { intro h,
    constructor,
    intro F,
    exact { 
      cone := { 
        X := ⊤_ C, 
        π := {
          app := λ X, false.elim ((fintype.card_eq_zero_iff.1 h) X), 
          }
        },
      is_limit := {lift := λ s, terminal.from s.X, fac' := sorry, uniq' := sorry}},
  },
sorry end⟩

#exit -- end of KB trying to catch up

-- Calle stuff below

⟨begin
  intro J,
  let x := classical.choice h
 in have card_lt : fintype.card J' < fintype.card J, refine fintype.card_subtype_lt J _, exact x, simp,
have J'_lims : limits.has_limits_of_shape (discrete J') C, refine finite_prod_of_binary_prod J',
refine ⟨_⟩, intro,
let F' := (discrete.lift (subtype.val : J' -> J)) ⋙ F,
have F'_has_lim : has_limit F', refine (has_limits_of_shape.has_limit F'),
let P := prod (limit F') (F.obj x),
refine {cone := _, is_limit := _},
{
refine {X := P, π := _},
  { refine {app := _, naturality' := _},
    { intro A, dsimp,
    exact (
    if H1 : A = x then by {rw H1, exact prod.snd}
    else prod.fst ≫ limit.π F' (⟨A, H1⟩))
    },
    dsimp [x, J'] at *, dsimp [x, J'], intros, split_ifs, substs h_1 h_2,
    dsimp [eq.mpr], simp, exfalso, apply h_2, rw ←h_1, rcases f, rcases f, exact f,
    exfalso, apply h_1, rw ←h_2, rcases f, rcases f, exact f.symm,
    simp, rcases f, rcases f, cases f, simp, },
},
{
refine {lift := _, fac' := _, uniq' := _},
  { exact (
    λ s, _
  )
  },
  {

  },
  {

  },
},

end
else _
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, @fintype.card x.1 x.2)⟩]}

/-  let MAP : (P ⟶ F'.obj ⟨A, H1⟩) := prod.fst ≫ limit.π F' (⟨A, H1⟩) in MAP) -/

#check subtype.val
end is_limit
end category_theory.limits