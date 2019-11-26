import category_theory.opposites
import category_theory.limits.shapes.products
import category_theory.limits.shapes.pullbacks

namespace category_theory
namespace category_theory.limits

open opposite


universes v u

variables {C : Type (u+1)} [𝒞 : large_category C]
include 𝒞

structure covering (U : C) :=
(ι : Type*)
(obj : ι → C)
(hom : Π i, obj i ⟶ U)

omit 𝒞

structure site (C : Type (u+1)) [𝒞 : large_category C] :=
(index : C → Type*)
(coverings : Π U, index U → covering U)
(pullback : ∀ {U V: C} (k : index U) (g : V ⟶ U), ∃ (l : index V), ∀ (j : (coverings V l).ι), 
∃ (i : (coverings U k).ι) (h : ((coverings V l).obj j) ⟶ ((coverings U k).obj i)), 
(coverings V l).hom j ≫ g = h ≫ ((coverings U k).hom i))

variables {D : Type (u+1)} [Dc : large_category D]
variables [products : limits.has_products.{u} D] [pullbacks : limits.has_pullbacks.{u} C]
variables {F : Cᵒᵖ ⥤ D}
include 𝒞 Dc products pullbacks

def asdf (U : C) (CU : covering U) (i j : CU.ι) := limits.pullback (CU.hom i) (CU.hom j)

/-def obj1 (U : C) (CU : covering U) := (limits.pullback (CU.hom i) (CU.hom j)) -/

def fan1 (U : C) (CU : covering U) := λ (i : CU.ι) (j : CU.ι), F.obj (op ( limits.pullback (CU.hom i) (CU.hom j)))

def intersection_prod (U : C) (CU : covering U) := limits.pi_obj (fan1 U CU)

/- TODO: 
Get maps from product of pullbacks to product of U_i
-/

end category_theory.limits
end category_theory