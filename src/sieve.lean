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
include 𝒞

 /- Maybe define sieve as a subfunctor? (but then I have to define subfunctor...)
 
 structure subfunctor (F : C ⥤ D) :=
(G : C ⥤ D)
(obj : ∀ (c : C), ) -/

/- Could potentially simplify hom definition by using hom_obj in hom_functor.lean somehow...-/
def sieve (X : C) := Π (Y : C), set ((functor.hom C).obj (op Y, X))

def id_sieve (X : C) : sieve X := λ (Y : C), {f | true}

set_option pp.universes true

def pullback_sieve (X Y : C) (f : Y ⟶ X) (S : sieve.{v} X) : sieve.{v} Y := λ Z, {g | g ≫ f ∈ S Z}

structure grothendieck_topology :=
(coverings : Π (X : C), set (sieve X))
(base_change : ∀ (X Y : C) (S : sieve X) (f : Y ⟶ X), S ∈ coverings X → (pullback_sieve X Y f S) ∈ coverings Y)
(local_character : ∀ (X : C) (S T : sieve X) (cover : S ∈ coverings X), ∀ (Y : C) (f : Y ⟶ X), 
f ∈ S Y ∧ (pullback_sieve X Y f S) ∈ coverings Y → T ∈ coverings X)
(id : ∀ (X : C), id_sieve X ∈ coverings X)

variable [pullbacks : limits.has_pullbacks.{v} C]
include pullbacks

end category_theory.functor
end category_theory.limits
end category_theory