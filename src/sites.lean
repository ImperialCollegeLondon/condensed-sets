import category_theory.opposites
import category_theory.limits.shapes.products
import category_theory.limits.shapes.pullbacks

namespace category_theory
namespace category_theory.limits

open opposite


universes w v u

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

structure covering (U : C) :=
(ι : Type v)
(obj : ι → C)
(hom : Π i, obj i ⟶ U)

set_option pp.universes true

structure site :=
(index : C → Type v)
(coverings : Π (U : C), index U → covering.{v} U)
(pullback : ∀ {U V: C} (k : index U) (g : V ⟶ U), ∃ (l : index V), ∀ (j : (coverings V l).ι), 
∃ (i : (coverings U k).ι) (h : ((coverings V l).obj j) ⟶ ((coverings U k).obj i)), 
(coverings V l).hom j ≫ g = h ≫ ((coverings U k).hom i))

variables {D : Type u} [Dc : category.{v} D]
variables [products : limits.has_products.{v} D] [pullbacks : limits.has_pullbacks.{v} C]
variables {F : Cᵒᵖ ⥤ D}
include Dc products pullbacks

def asdf (U : C) (CU : covering.{v} U) (i j : CU.ι) := limits.pullback (CU.hom i) (CU.hom j)

/-def obj1 (U : C) (CU : covering U) := (limits.pullback (CU.hom i) (CU.hom j)) -/

def fan1 (U : C) (CU : covering.{v} U) := λ (k : CU.ι × CU.ι), F.obj (op ( limits.pullback (CU.hom k.1) (CU.hom k.2)))

def intersection_prod (U : C) (CU : covering.{v u} U) := limits.pi_obj.{v u} (@fan1 _ _ _ _ _ _ F U CU)

/- TODO: 
Get maps from product of pullbacks to product of U_i
-/

end category_theory.limits
end category_theory