import tactic.finish


-- EXAMPLE 1: transfering ordering <= from nat to custom nat (bijection)
-- this example is based on the one in the article by Zimmermann and Herbelin, 2015
namespace example1

-- a custom type N that is the natural numbers, with an ordering like <=
def N : Type := sorry
def ordern : N → N → Prop := sorry

-- functions mapping N to nat and back
def nto : N → nat := sorry
def nof : nat → N := sorry

-- axioms needed for transfer:
-- the nto and nof are inverses
axiom ax1 : ∀ n : nat, nto(nof(n)) = n
axiom ax2 : ∀ x : N, nof(nto(x)) = x
-- ordering is preserved by the mapping
axiom ax3 : ∀ x y : N, ordern x y → nto x <= nto y 
axiom ax4 : ∀ m n : nat, m <= n → ordern (nof m) (nof n)

--suppose we have proven transitivity for <= in nat, and want to now prove it in N without doing the proof again
theorem transitiveorder_nat : ∀ x y z : nat, x <= y → y <= z → x <= z := sorry

theorem transitiveorder_N : ∀ x y z : N, ordern x y → ordern y z → ordern x z :=
begin
  intros,
  rw← ax2 x,
  rw← ax2 z,
  apply ax4,
  apply transitiveorder_nat _ (nto y) _;
  finish using [ax3]
end

--we could also prove it the other way, the proof is symmetric: using ax1 instead of ax2 and swapping ax3 and ax4
theorem transitiveorder_nat' : ∀ x y z : nat, x <= y → y <= z → x <= z := 
begin 
  intros,
  rw← ax1 x,
  rw← ax1 z,
  apply ax3,
  apply transitiveorder_N _ (nof y) _;
  finish using [ax4]
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
-- mapping is surjective
axiom surjectivemap : function.surjective ztoz2
-- mapping respects add and even (there must be transfer axioms for every operation and predicate in the theorem)
axiom transfer_add : ∀ m n : int, (ztoz2 m).add (ztoz2 n) = ztoz2(m + n)
axiom eventoz2 : ∀ n : int, even n → Z2.even (ztoz2 n)
axiom evenfromz2 : ∀ n : int, Z2.even (ztoz2 n) → even n  -- specific wording of the axioms makes the proof go nicely

-- theorem about adding two odd integers, now we want the same result in Z2
theorem thetheoremforint : ∀ m n : int, ¬ even m → ¬ even n → even (m + n) := sorry

theorem thetheoremforZ2 : ∀ x y : Z2, ¬ Z2.even x → ¬ Z2.even y → Z2.even (Z2.add x y) := 
begin
  intros,
  rw [← classical.some_spec (surjectivemap x)] at *,
  rw [← classical.some_spec (surjectivemap y)] at *,
  rw transfer_add,
  apply eventoz2,
  apply thetheoremforint;
  finish using [eventoz2]
end

-- the other direction can also be shown
theorem thetheoremforint' : ∀ x y : int, ¬ even x → ¬ even y → even (x + y) := 
begin
  intros,
  apply evenfromz2,
  rw← transfer_add,
  apply thetheoremforZ2;
  finish using [evenfromz2]
end

end example2


-- EXAMPLE 3: even theorem but with injection natural numbers to integers
namespace example3

definition even (n : nat) : Prop := n % 2 = 0
definition evenint (x : int) : Prop := x % 2 = 0

-- mapping between nat and int
def ntoi : nat → int := int.of_nat --in all example cases the implementations are optional and not necessary for the proofs (nice to have for computation later?)
def nofi : int → nat := int.nat_abs

-- axioms needed for transfer:
axiom inverse1way : ∀ n : nat, nofi(ntoi n) = n
-- respect add
axiom transfer_add : ∀ x y : int, nofi x + nofi y = nofi (x + y)
-- respect even
axiom eventoint: ∀ x : int, even (nofi x) → evenint x
axiom evenfromint : ∀ x : int, evenint x → even (nofi x)

theorem thetheoremfornat : ∀ m n : nat, ¬ even m → ¬ even n → even (m + n) := sorry

theorem thetheoremforint : ∀ x y : int, ¬ evenint x → ¬ evenint y → evenint (x + y) :=
begin
  intros,
  apply eventoint,
  rw← transfer_add,
  apply thetheoremfornat;
  finish using [eventoint]
end

theorem thetheoremfornat' : ∀ m n : nat, ¬ even m → ¬ even n → even (m + n) :=
begin
  intros,
  rw← inverse1way m at *,
  rw← inverse1way n at *,
  rw transfer_add,
  apply evenfromint,
  apply thetheoremforint;
  finish using [evenfromint]
end

end example3


-- EXAMPLE 4: the ordering theorem but with int and nat
namespace example4

-- mapping between nat and int
def ntoi : nat → int := int.of_nat
def nofi : int → nat := int.nat_abs

-- axioms needed for transfer:
-- 1 direction is invertible
axiom inverse1way : ∀ n : nat, nofi(ntoi n) = n

-- ordering is not really preserved by the mapping, which poses a problem
-- ∀ x y : int, x <= y → nofi x <= nofi y     does not hold
-- ∀ x y : int, nofi x <= nofi y → x <= y     does not hold
-- axiom order_ntoi : ∀ m n : nat, m <= n → ntoi m <= ntoi n      not useful
axiom order_nofi : ∀ x y : int, x <= y → nofi x <= nofi y ∨ nofi y <= nofi x    -- doesn't go anywhere

-- transfer approach does not seem to work for this problem
-- idea: smaller axioms ie x<=y and x>0 → nofi x <= nofi y
--                         x<=y and x<0 and y>0 → either is larger
--                         x<=y and x<0 and y<0 → nofi x >= nofi y
--   and split on cases <0 >0
-- doesn't seem too useful either 

theorem transitiveorder_nat : ∀ a b c : nat, a <= b → b <= c → a <= c := sorry

theorem transitiveorder_int : ∀ x y z : int, x <= y → y <= z → x <= z :=
begin
  intros,
  have hnxy : nofi x <= nofi y ∨ nofi y <= nofi x := by apply order_nofi _ _ a,
  have hnyz : nofi y <= nofi z ∨ nofi z <= nofi y := by apply order_nofi _ _ a_1,
  cases hnxy; cases hnyz,

  have hnxz : nofi x <= nofi z := begin apply transitiveorder_nat _ _ _ hnxy hnyz end,
  repeat {sorry},
end

theorem transitiveorder_nat' : ∀ a b c : nat, a <= b → b <= c → a <= c :=
begin
  intros,
  rw← inverse1way a at *,
  rw← inverse1way b at *,
  rw← inverse1way c at *,
  sorry
end

end example4