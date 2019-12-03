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
structure sieve (X : C) := 
(map : Π (Y : C), set (Y ⟶ X))
(comp : ∀ (Y Z: C) (g : Y ⟶ Z) (f ∈ map Z), g ≫ f ∈ map Y)

def id_sieve (X : C) : sieve.{v} X := ⟨λ (Y : C), {f | true}, by tidy⟩

def pullback_sieve (X Y : C) (f : Y ⟶ X) (S : sieve.{v} X) : sieve.{v} Y := ⟨λ Z, {g | g ≫ f ∈ S.map Z}, by {tidy, apply S.comp, exact H}⟩

structure grothendieck_topology :=
(coverings : Π (X : C), set (sieve.{v} X))
(base_change : ∀ (X Y : C) (S : sieve.{v} X) (f : Y ⟶ X), S ∈ coverings X → (pullback_sieve X Y f S) ∈ coverings Y)
(local_character : ∀ (X : C) (S T : sieve.{v} X) (cover : S ∈ coverings X), ∀ (Y : C) (f : Y ⟶ X), 
f ∈ S.map Y ∧ (pullback_sieve X Y f S) ∈ coverings Y → T ∈ coverings X)
(id : ∀ (X : C), id_sieve X ∈ coverings X)

end category_theory.functor
end category_theory.limits
end category_theory