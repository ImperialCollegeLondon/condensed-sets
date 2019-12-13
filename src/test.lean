import category_theory.limits.shapes.products

open category_theory
open opposite

section test
universes v
variables {C : Type v} [CCat : category.{v} C]
variables {D : Type v} [DCat : category.{v} D]
variables [products : limits.has_products.{v} D]
include CCat

structure test_sieve (X : C) := 
(map : Π (Y : C), set (Y ⟶ X))
(comp : ∀ (Y Z: C) (g : Y ⟶ Z) (f ∈ map Z), g ≫ f ∈ map Y)

structure test_domain {X : C} (S : test_sieve X) :=
(Y : C)
(f : Y ⟶ X)
(in_cover : f ∈ S.map Y)

#check ∏ (λ A : D, A)

include products DCat

variable F : Cᵒᵖ ⥤ D

def test_map {U : C} (S : test_sieve U) : F.obj (op U) ⟶ ∏ (λ k : test_domain S, F.obj (op k.Y))
    := limits.pi.lift (λ k : test_domain S, F.map k.f.op )

def test_mono {U : C} (S : test_sieve U) : Prop := mono (test_map F S)

def test_prop (coverings : Π (X : C), set (test_sieve X)) :
    ∀ {U : C} (S : test_sieve U) (S ∈ coverings U), test_mono F S := sorry


end test