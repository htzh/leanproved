/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data .extra .hom .perm

namespace group
open algebra

section def
variables {G S : Type}
variable [g : group G]
include g
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS
variable [h : hom_class G (perm S)]

end def

end group
