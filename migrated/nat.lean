
import theories.number_theory.primes data.nat
open nat eq.ops
namespace shadow
section order

lemma lt_succ_of_lt {i j : nat} : i < j → i < succ j :=
assume Plt, lt.trans Plt (self_lt_succ j)

end order

section power

lemma pow_dvd_of_pow_succ_dvd {p i n : nat} : p^(succ i) ∣ n → p^i ∣ n :=
assume Psuccdvd,
assert Pdvdsucc : p^i ∣ p^(succ i), from by rewrite [pow_succ]; apply dvd_of_eq_mul; apply rfl,
dvd.trans Pdvdsucc Psuccdvd

lemma dvd_of_pow_succ_dvd_mul_pow {p i n : nat} (Ppos : p > 0) :
  p^(succ i) ∣ (n * p^i) → p ∣ n :=
by rewrite [pow_succ']; apply dvd_of_mul_dvd_mul_right; apply pow_pos_of_pos _ Ppos

end power

section prime

end prime
end shadow
