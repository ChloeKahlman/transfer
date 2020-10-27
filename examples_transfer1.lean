import tactic.finish

import .transfer

-- EXAMPLE 1: transfering ordering <= from nat to custom nat (bijection)
-- this example is based on the one in the article by Zimmermann and Herbelin, 2015
namespace example1

-- a custom type N that is the natural numbers, with an ordering like <=
def N : Type := sorry
def ordern : N → N → Prop := sorry

-- functions mapping N to nat and back
def nto : N → nat := sorry
def nof : nat → N := sorry

axiom nto_surj : function.surjective nto
axiom nof_surj : function.surjective nof
axiom le_ordern_nof : ∀ m n : nat, m <= n → ordern (nof m) (nof n)
axiom ordern_nof_le : ∀ m n : nat, ordern (nof m) (nof n) → m <= n

--suppose we have proven transitivity for <= in nat, and want to now prove it in N without doing the proof again
theorem transitiveorder_nat : ∀ x y z : nat, x <= y → y <= z → x <= z := sorry

theorem transitiveorder_N : ∀ x y z : N, ordern x y → ordern y z → ordern x z :=
begin
  transfer.transfer1 ``(nof_surj) [``(ordern_nof_le _ _)] [``(le_ordern_nof), ``(transitiveorder_nat)],
end

--we could also prove it the other way, the proof is symmetric: using ax1 instead of ax2 and swapping ax3 and ax4
theorem transitiveorder_nat' : ∀ x y z : nat, x <= y → y <= z → x <= z := 
begin 
  transfer.transfer1 ``(nof_surj) [``(ordern_nof_le _ _)] [``(le_ordern_nof), ``(transitiveorder_nat)],
  -- ! exact same command
end

end example1


-- EXAMPLE 2: transfer the theorem that odd+odd=even from z to z mod 2 and back.
namespace example2

definition even (n : int) : Prop := n % 2 = 0

-- a custom type Z/2Z, with operation add and predicate even
inductive Z2 : Type
| zero : Z2
| one : Z2

open Z2

def Z2.add : Z2 → Z2 → Z2
| zero y := y
| one zero := one 
| one one := zero

inductive Z2.even : Z2 → Prop
| zeroiseven : Z2.even zero

-- mapping from int to Z2 (no inverse mapping)
def ztoz2 : int → Z2 := λ n, if n % 2 = 0 then zero else one

-- axioms needed for transfer:
axiom surjectivemap : function.surjective ztoz2
-- axiom transfer_add : ∀ m n : int, (ztoz2 m).add (ztoz2 n) = ztoz2(m + n)
axiom transfer_add' : ∀ m n : int, ztoz2(m + n) = (ztoz2 m).add (ztoz2 n)
axiom eventoz2 : ∀ n : int, even n → Z2.even (ztoz2 n)
axiom evenfromz2 : ∀ n : int, Z2.even (ztoz2 n) → even n  -- specific wording of the axioms makes the proof go nicely

-- theorem about adding two odd integers, now we want the same result in Z2
theorem thetheoremforint : ∀ m n : int, ¬ even m → ¬ even n → even (m + n) := sorry

theorem thetheoremforZ2 : ∀ x y : Z2, ¬ Z2.even x → ¬ Z2.even y → Z2.even (Z2.add x y) := 
begin
  transfer.transfer1 ``(surjectivemap) [``(transfer_add'), ``(eventoz2)] [``(thetheoremforint), ``(eventoz2)],
end

-- the other direction can also be shown
theorem thetheoremforint' : ∀ x y : int, ¬ even x → ¬ even y → even (x + y) := 
begin
    transfer.transfer1 ``(surjectivemap) [``(transfer_add'), ``(eventoz2)] [``(thetheoremforint), ``(eventoz2)],
end

end example2


-- EXAMPLE 3: even theorem but with injection natural numbers to integers
namespace example3

definition even (n : nat) : Prop := n % 2 = 0
definition evenint (x : int) : Prop := x % 2 = 0

-- mapping between nat and int
def ntoi : nat → int := int.of_nat
def nofi : int → nat := int.nat_abs

-- axioms needed for transfer:
-- axiom inverse1way : ∀ n : nat, nofi(ntoi n) = n
axiom nofi_surj : function.surjective nofi
axiom transfer_add : ∀ x y : int, nofi x + nofi y = nofi (x + y)
axiom eventoint: ∀ x : int, even (nofi x) → evenint x
axiom evenfromint : ∀ x : int, evenint x → even (nofi x)

theorem thetheoremfornat : ∀ m n : nat, ¬ even m → ¬ even n → even (m + n) := sorry

theorem thetheoremforint : ∀ x y : int, ¬ evenint x → ¬ evenint y → evenint (x + y) :=
begin
  transfer.transfer1 ``(nofi_surj) [``(eventoint), ``(transfer_add)] [``(thetheoremfornat), ``(eventoint)]
end

theorem thetheoremfornat' : ∀ m n : nat, ¬ even m → ¬ even n → even (m + n) :=
begin
  transfer.transfer1 ``(nofi_surj) [``(eventoint), ``(transfer_add)] [``(thetheoremfornat), ``(eventoint)]
end

end example3