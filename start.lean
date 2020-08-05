import topology.basic

#check topological_space

#eval 1+1

theorem add_one_one : 1 + 1 = 2 := by refl

-- this is a comment

-- a type N
def N : Type

-- a type nat
--nat is a type

-- order on N
def ordern : N → N → Prop

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
    apply thetheoremfornat (nto x) (nto y) (nto z),
    apply ax3,
    assumption,
    apply ax3,
    assumption,
end