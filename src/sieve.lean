import category_theory.opposites
import category_theory.hom_functor
import category_theory.limits.shapes.products
import category_theory.limits.shapes.pullbacks

namespace category_theory
namespace category_theory.limits
namespace category_theory.functor

open opposite


universes v u

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞 Dc

 /- Maybe define sieve as a subfunctor? (but then I have to define subfunctor...)
 
 structure subfunctor (F : C ⥤ D) :=
(G : C ⥤ D)
(obj : ∀ (c : C), ) -/

/- Could potentially simplify hom definition by using hom_obj in hom_functor.lean somehow...-/
def sieve (c : C) := Π (U : C), set ((functor.hom C).obj (op (U), c))

set_option pp.universes true

/- def pullback_sieve (X Y : C) (f : Y ⟶ X) (S : sieve.{v} X) : sieve.{v} Y := λ U, _ -/

variable [pullbacks : limits.has_pullbacks.{v} C]
include pullbacks

end category_theory.functor
end category_theory.limits
end category_theory