import tactic
open tactic.interactive


namespace transfer

#check pexpr

meta def transfer1 (surjectivemap : pexpr): tactic unit := 
do
-- move things to assumptions
  tactic.intros,

-- get axioms from arguments?
  -- proof of surjection

--in some order:
  -- find variables
  l ← tactic.local_context,
 -- l.mmap' (λ h, do tactic.trace "Name:", tactic.trace h, tactic.trace "Type:", tactic.infer_type h >>= tactic.trace),
  l.mmap' (λ h, tactic.try (tactic.interactive.rw (rw_rules_t.mk [(rw_rule.mk ⟨0,0⟩ tt ``(classical.some_spec (%%surjectivemap %%h)))] none) interactive.loc.wildcard))

--(← classical.some_spec (surjectivemap h))
 --(← classical.some_spec (surjectivemap h))
  -- for each, try to use surj axiom to transfer them



  -- find and transfer the operations

--apply the theorem

--finish


-- a custom type N that is the natural numbers, with an ordering like <=
def N : Type := sorry
def ordern : N → N → Prop := sorry

-- functions mapping N to nat and back
def nto : N → nat := sorry
def nof : nat → N := sorry

axiom nto_surj : function.surjective nto
axiom nof_surj : function.surjective nof

theorem transitiveorder_nat : ∀ x y z : nat, x <= y → y <= z → x <= z := sorry

theorem transitiveorder_N : ∀ x y z : N, ordern x y → ordern y z → ordern x z :=
begin
  intros,
  transfer1 ``(nof_surj),
  sorry
end



end transfer