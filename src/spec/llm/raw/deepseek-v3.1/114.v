
Require Import Coq.Lists.List.
Require Import Coq.Arith.MinMax.
Require Import Coq.ZArith.ZArith.

Definition minSubArraySum_spec (nums : list Z) (result : Z) : Prop :=
  exists l, exists sub, In sub (sublists l) /\ sub <> nil /\ 
  result = fold_left Z.add sub 0 /\ 
  (forall sub', In sub' (sublists nums) -> sub' <> nil -> 
   result <= fold_left Z.add sub' 0).
