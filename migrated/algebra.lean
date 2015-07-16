/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group
open algebra

namespace migration

section group

variables {A : Type} [ambA : group A]
include ambA

theorem eq_inv_of_mul_eq_one {a b : A} (H : a * b = 1) : a = b⁻¹ :=
begin rewrite [eq_inv_iff_eq_inv], apply eq.symm, exact inv_eq_of_mul_eq_one H end

end group

end migration
