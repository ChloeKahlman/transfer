import tactic

open tactic.interactive
open interactive.types

open interactive

open lean.parser


def mylist : list nat := [0,1]

#check pexpr
#check tactic.interactive.apply

meta def tactic.interactive.apply_at  (h : parse texpr) (f : parse (tk "using" *> texpr)) : tactic unit := 
do
  h' ← tactic.i_to_expr_for_apply h,
  tactic.interactive.replace (expr.local_pp_name h') none (f h)

#check interaction_monad_orelse

meta def my_orelse {α : Type*} (t₁ t₂ : tactic α) : tactic α :=
λ s, interaction_monad.result.cases_on (t₁ s)
  interaction_monad.result.success
  (λ e₁ ref₁ s', interaction_monad.result.cases_on ((trace ((e₁.get_or_else sorry) ()) >> t₂) s)
     interaction_monad.result.success
     interaction_monad.result.exception)

infix `<||>` : 2 := my_orelse 

namespace transfer

meta def transfer1 (surjectivemap : pexpr) (operations : list pexpr) (finishing : list pexpr) : tactic unit := 
do
-- move things to assumptions
  tactic.intros,

-- get axioms from arguments?
  -- proof of surjection

--in some order:
  -- find variables
  l ← tactic.local_context,
 -- l.mmap' (λ h, do tactic.trace "Name:", tactic.trace h, tactic.trace "Type:", tactic.infer_type h >>= tactic.trace),
  l.mmap' (λ h, tactic.try (tactic.interactive.rw (rw_rules_t.mk [(rw_rule.mk ⟨0,0⟩ tt ``(classical.some_spec (%%surjectivemap %%h)))] none) interactive.loc.wildcard)),
  
  -- tactic.interactive.rw (rw_rules_t.mk [(rw_rule.mk ⟨0,0⟩ tt ``(operations))] none) interactive.loc.wildcard
  -- find and transfer the operations in the goal

  --(option.cases_on (operations.nth 0) (tactic.fail "fail") (tactic.i_to_expr_for_apply >=> tactic.apply) : tactic (list (name × expr))),
  --skip
  --,

  trace_state,

  tactic.repeat (
    operations.foldr (
      λ op rest, 
        rest
        <||>
        (tactic.i_to_expr_for_apply >=> tactic.apply) op >> skip
        <||>
        tactic.interactive.rw (rw_rules_t.mk [(rw_rule.mk ⟨0,0⟩ tt op)] none) interactive.loc.wildcard
        <||>
        ( do
        l2 ← tactic.local_context,
        
        l2.foldr (λ h rest2, rest2 <||> tactic.interactive.apply_at (to_pexpr h) op) (tactic.fail "foldr2 fail"),

        skip
        )
    ) (tactic.fail "oeps")
  <||> tactic.fail "exit repeat"),

  tactic.interactive.finish [] finishing,

  skip

  --tactic.repeat (
  --operations.mmap' (λ h, tactic.try 
  --  (
      --(tactic.applyc `h) 
      --<|> 
  --    (tactic.interactive.rw (rw_rules_t.mk [(rw_rule.mk ⟨0,0⟩ tt ``(classical.some_spec (%%surjectivemap %%h)))] none) interactive.loc.wildcard)
  --  )
  --)
  --)
  --,

--apply the theorem

--finish
--skip
end transfer

--open parser

--meta def tactic.interactive.apply_at  (h : parse ident) (f : parse texpr) : tactic unit := 
--do
--  tactic.interactive.replace h none (f ( h))

--name naar tactic.expr = get_local in tactic.lean

theorem test (a b : Type) (ha : a) (hab : a → b) : b := 
begin
  --apply_at ha using hab,
  apply_at hab ha using id,
  assumption,
  -- assumption, --finding ha_1
end  


def N : Type := sorry
def ordern : N → N → Prop := sorry
def nto : N → nat := sorry
def nof : nat → N := sorry

axiom nto_surj : function.surjective nto
axiom nof_surj : function.surjective nof
axiom le_ordern_nof : ∀ m n : nat, m <= n → ordern (nof m) (nof n)
axiom le_ordern_nof_iff : ∀ m n : nat,  m <= n ↔ ordern (nof m) (nof n) --temp hack
axiom ordern_nof_le : ∀ m n : nat, ordern (nof m) (nof n) → m <= n

theorem transitiveorder_nat : ∀ x y z : nat, x <= y → y <= z → x <= z := sorry

theorem transitiveorder_N : ∀ x y z : N, ordern x y → ordern y z → ordern x z :=
begin
  -- intros,
  -- rw [← classical.some_spec (nof_surj x)] at *,
  -- rw [← classical.some_spec (nof_surj y)] at *,
  -- rw [← classical.some_spec (nof_surj z)] at *,

  -- apply_at a using ordern_nof_le _ _,
  -- apply_at a_1 using ordern_nof_le _ _,

  -- apply le_ordern_nof,
  -- finish using [transitiveorder_nat],

  transfer.transfer1 ``(nof_surj) [``(ordern_nof_le _ _)] [``(le_ordern_nof), ``(transitiveorder_nat)],

  --``(le_ordern_nof_iff)

  --have b := ordern_nof_le _ _ a,
  --have b_1 := ordern_nof_le _ _ a_1,
  
  --apply le_ordern_nof,
  --finish using transitiveorder_nat,
end





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
  transfer.transfer1 ``(surjectivemap) [``(transfer_add), ``(eventoz2)] [``(eventoz2), ``(thetheoremforint)],
  
  --apply met not 

  -- intros,
  -- rw [← classical.some_spec (surjectivemap x)] at *,
  -- rw [← classical.some_spec (surjectivemap y)] at *,
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





end transfer