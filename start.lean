--lean is working
import topology.basic
#check topological_space
#eval 1+1
theorem add_one_one : 1 + 1 = 2 := by refl

--EXAMPLE 1: transfering order from nat to custom nat (bijection)
namespace example1

-- a type N
def N : Type := sorry

-- a type nat
--nat is a type

-- order on N
def ordern : N → N → Prop := sorry

-- order on nat
--nat has an order

-- function nto
def nto : N → nat := sorry

-- function nof
def nof : nat → N := sorry

axiom ax1 : ∀ x : nat, nto(nof(x)) = x

axiom ax2 : ∀ x : N, nof(nto(x)) = x

axiom ax3 : ∀ x y : N, ordern x y → nto x <= nto y 

axiom ax4 : ∀ x y : nat, x <= y → ordern (nof x) (nof y)

theorem thetheoremfornat : ∀ x y z : nat, x <= y → y <= z → x <= z := sorry

theorem thetheoremforN : ∀ x y z : N, ordern x y → ordern y z → ordern x z :=
begin
    intros,
    rw← ax2 x,
    rw← ax2 z,
    apply ax4,
    apply thetheoremfornat (nto x) (nto y) (nto z);
    finish using [ax3],
    --apply ax3,
    --assumption,
    --apply ax3,
    --assumption,
end

--TODO thetheoremfornatagain
end example1

--EXAMPLE 2: transfer the theorem that odd+odd=even from z to z mod 2 and back.
namespace example2

--even and odd on Z
definition even (n : int) : Prop := n % 2 = 0
--definition odd (n : int) : Prop := n % 2 = 1

--type Z/2Z
inductive Z2 : Type
| zero : Z2
| one : Z2

def Z2.add : Z2 → Z2 → Z2
| Z2.zero y := y
| Z2.one Z2.zero := Z2.one 
| Z2.one Z2.one := Z2.zero

open Z2

--even on z/2z
inductive evenZ2 : Z2 → Prop
| zeroiseven : evenZ2 zero

--transfer function (mod 2)
def ztoz2 : int → Z2 := λ n, if n % 2 = 0 then zero else one

--transfer respects add
axiom transfer_add : ∀ m n : int, (ztoz2 m).add (ztoz2 n) = ztoz2(m + n)

--DIRECTION Z to Z2
axiom eventransfertoz2 : ∀ n : int, even n → evenZ2 (ztoz2 n)

--DIRECTION Z2 to Z
axiom eventransferfromz2  : ∀ x : Z2, ∀ y : int, evenZ2 x → ztoz2 y = x → even y

-- axiom transfer_add_2 : ∀ x y : Z2, ∀ m n : int, ztoz2 m = x → ztoz2 n = y → x.add y = ztoz2 (m + n)

axiom ztoz2surj : function.surjective ztoz2

--theorem about even numbers
theorem thetheoremforint : ∀ m n : int, ¬ even m → ¬ even n → even (m + n) := sorry

--theorem about even numbers in z2, using only axioms, the proven theorem in int, and assumptions
theorem thetheoremforZ2 : ∀ x y : Z2, ¬ evenZ2 x → ¬ evenZ2 y → evenZ2 (add x y) := 
begin
    intros,
    --pick numbers such that m % 2 = x, n % 2 = y
    --rw transfer_add_2,
    --apply eventransfertoz2,
    --apply thetheoremforint,
    let m := classical.some (ztoz2surj x),
    let n := classical.some (ztoz2surj y),
    have mx : ztoz2 m = x := classical.some_spec(ztoz2surj x),
    have ny : ztoz2 n = y := classical.some_spec(ztoz2surj y),

    rw← mx,
    rw← ny,

    rw transfer_add,
    apply eventransfertoz2,
    apply thetheoremforint,

   -- have : ¬ even m,
   { finish using [eventransfertoz2] },
   -- have : ¬ even n,
   { finish using [eventransfertoz2] },

   
   -- assumption,
   -- assumption,
   -- assumption,
    --have test: ¬ even 1 := sorry,
    --apply test,
    --have test: ¬ even 1 := sorry,
    --apply test,
  --  sorry --  WIP 
end

theorem thetheoremforZ2_2 : ∀ x y : Z2, ¬ evenZ2 x → ¬ evenZ2 y → evenZ2 (add x y) := 
begin
    intros,
    have surj : function.surjective ztoz2 := sorry,

    rw [← classical.some_spec (surj x)] at *,
    rw [← classical.some_spec (surj y)] at *,
    rw transfer_add,
    apply eventransfertoz2,
    apply thetheoremforint;

    finish using [eventransfertoz2],
end

    --adding two odd numbers in Z2, so one.add one
    --*any number* that % 2 equals one is odd, --map is surjective so the numbers exist
    --odd plus odd = even
    --even number % 2 is even too
    --this result is equal to adding in Z2

    --classical.some to pick one of the ints 

theorem thetheoremforZ2again : ∀ x y : Z2, ¬ evenZ2 x → ¬ evenZ2 y → evenZ2 (add x y) := 
begin 
  --practice proof
  intros,
  cases x,
  { apply false.elim,
    apply a,
    apply evenZ2.zeroiseven},
  { cases y,
      { apply false.elim,
        apply a_1,
       apply evenZ2.zeroiseven},
      { simp [Z2.add],
        apply evenZ2.zeroiseven}},
end

--proof using only the theorem in Z2, axioms, and assumptions
theorem thetheoremforintagain : ∀ x y : int, ¬ even x → ¬ even y → even (x + y) := 
begin
  intros,

  apply eventransferfromz2,

  have addinZ2iseven : evenZ2 ((ztoz2 x).add (ztoz2 y)) := 
      begin
        apply thetheoremforZ2again, 

        intro bla2,
        apply a,
        apply eventransferfromz2,
        apply bla2,
        simp,

        intro bla2,
        apply a_1,
        apply eventransferfromz2,
        apply bla2,
        simp,
      end,

  apply addinZ2iseven,

  simp [transfer_add],
end

end example2

namespace example3
-- EXAMPLE 3: do an example with injection natural numbers to integers
-- even op natuurlijke getallen naar even op integers

--nat is a type
--int is a type

--even prop
definition even (n : nat) : Prop := n % 2 = 0
definition evenint (x : int) : Prop := x % 2 = 0

--transfer functions
def ntoi : nat → int := int.of_nat --implementations optional
def nofi : int → nat := int.nat_abs

axiom inverse1way : ∀ n : nat, nofi(ntoi n) = n

--transfer lemmas
--axiom transfer_add : ∀ m n : nat, ntoi m + ntoi n = ntoi (m + n)
axiom transfer_add2 : ∀ x y : int, nofi x + nofi y = nofi (x + y)

--axiom eventoint : ∀ n : nat, even n → evenint (ntoi n)
axiom evenfromint : ∀ x : int, evenint x → even (nofi x)

theorem thetheoremfornat : ∀ m n : nat, ¬ even m → ¬ even n → even (m + n) := sorry

theorem thetheoremforint : ∀ x y : int, ¬ evenint x → ¬ evenint y → evenint (x + y) :=
begin
  intros,

  --Cant do this:
  --let m be such that ntoi m = x
  --let n be such that ntoi n = y

  --let m = nofi x
  --let n = nofi y





  -- old
  --have test: even (nofi x + nofi y) :=
  --begin
  --  apply thetheoremfornat,

  --  intro b,
  --  apply a,
    --rw← inverse1way (nofi x) at *,

    --finish using [eventoint],
    --rw transfer_add2,
  --sorry, sorry  
  --end,
end

theorem thetheoremfornatagain : ∀ m n : nat, ¬ even m → ¬ even n → even (m + n) :=
begin
  intros,
  rw← inverse1way m at *,
  rw← inverse1way n at *,
  rw transfer_add2,
  apply evenfromint,
  apply thetheoremforint;
  finish using [evenfromint],
end   

end example3