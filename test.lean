import data.nat
open nat

theorem mul_mod_eq_mod_mul_mod (m n k : nat) : (m * n) mod k = ((m mod k) * n) mod k :=
by_cases_zero_pos k
  (by rewrite [*mod_zero])
  (take k, assume H : k > 0,
    (calc
      (m * n) mod k = (((m div k) * k + m mod k) * n) mod k : eq_div_mul_add_mod
            ... = ((m mod k) * n) mod k                     :
                    by rewrite [mul.right_distrib, mul.right_comm, add.comm, add_mul_mod_self H]))

theorem eq_zero_or_eq_one_of_lt_two : ∀ {n : nat}, n < 2 → n = 0 ∨ n = 1 := dec_trivial

definition even (n : nat) : Prop := n mod 2 = 0

definition odd (n : nat) : Prop := n mod 2 = 1

theorem even_or_odd (n : nat) : even n ∨ odd n := eq_zero_or_eq_one_of_lt_two (mod_lt dec_trivial)

theorem even_of_exists_eq_two_mul {n : nat} (H : ∃ m, n = 2 * m) : even n :=
obtain m (H1 : n = 2 * m), from H,
calc
  n mod 2 = 2*m mod 2 : H1
      ... = 0         : mul_mod_right

theorem exists_eq_two_mul_of_even {n : nat} (H : even n) : ∃ m, n = 2 * m :=
exists.intro (n div 2)
  (calc
    n     = (n div 2) * 2 + n mod 2 : eq_div_mul_add_mod
      ... = 2*(n div 2)             : by rewrite [↑even at H, H, add_zero, mul.comm])

theorem even_of_even_square {n : nat} (H : even (n * n)) : even n :=
or.elim (even_or_odd n) (assume H, H)
  (assume H1 : n mod 2 = 1,
    have H2 : 0 = 1, from calc
      0     = n * n mod 2           : H
        ... = ((n mod 2) * n) mod 2 : mul_mod_eq_mod_mul_mod
        ... = 1                     : by rewrite [H1, one_mul, H1],
    absurd H2 dec_trivial)

theorem sqrt2_irrational (m : nat) : ∀ n : nat, n * n = 2 * m * m → m = 0 :=
nat.strong_induction_on m
  (take m,
    by_cases_zero_pos m (λ IH n H, rfl)
      (take m,
        assume (mpos : m > 0),
        assume IH : ∀ {m'}, m' < m → (∀ {n}, n * n = 2 * m' * m' → m' = 0),
        take n,
        assume H : n * n = 2 * m * m,
        have H1 : even (n * n),
          from even_of_exists_eq_two_mul (exists.intro _ (eq.subst !mul.assoc H)),
        have H2 : even n, from even_of_even_square H1,
        obtain k (H3 : n = 2 * k), from exists_eq_two_mul_of_even H2,
        have H4 : 2 * (m * m) = 2 * (2 * k * k),
          by rewrite [-mul.assoc, -H, H3, *mul.assoc, mul.left_comm k],
        assert H5 : m * m = 2 * k * k, from !eq_of_mul_eq_mul_left dec_trivial H4,
        have H6 : k < m, from
          lt_of_not_le
            (assume H' : k ≥ m,
              have H1' : k > 0, from lt_of_lt_of_le mpos H',
              have H2' : k * k ≥ m * m, from mul_le_mul H' H',
              assert H3' : 2 * (k * k) > 1 * (m * m),
                from mul_lt_mul_of_lt_of_le (mul_pos H1' H1') dec_trivial H2',
              have H4' : 2 * k * k > 2 * k * k,
                by revert H3'; rewrite [H5, one_mul, mul.assoc]; intros; assumption,
              absurd H4' !lt.irrefl),
        assert H7 : k = 0, from IH H6 H5,
        have H8 : m * m = 0, by rewrite [H5, H7, mul_zero],
        show m = 0, from iff.mp !or_self (eq_zero_or_eq_zero_of_mul_eq_zero H8)))