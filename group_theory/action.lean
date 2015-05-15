import algebra.group data.set .extra

namespace algebra
namespace group
section perm
open set function
variable {A : Type}
structure perm (A : Type) : Type :=
(f : A → A) (is_perm : @bijective A A f)
attribute perm.f [coercion]

definition perm.compose (g f : perm A) : perm A := 
  perm.mk (g∘f) (bijective_compose (perm.is_perm g) (perm.is_perm f))
local infix `^` := perm.compose
theorem perm.assoc (h g f : perm A) : h ^ g ^ f = h ^ (g ^ f) := 
        begin
          rewrite ↑perm.compose
        end
check @semigroup.mk
definition mk_perm := @semigroup.mk (perm A) perm.compose perm.assoc
end perm



end group
end algebra
