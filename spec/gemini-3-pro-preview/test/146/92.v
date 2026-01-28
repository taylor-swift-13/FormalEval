Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero (operations : list Z) : Z :=
  let fix aux (balance : Z) (ops : list Z) : Z :=
    match ops with
    | [] => 1
    | op :: rest =>
      let new_balance := balance + op in
      if new_balance <? 0 then 0 else aux new_balance rest
    end
  in aux 0 operations.

Example test_below_zero_2 : below_zero [101; -35; 16; 44; -67; 42] = 1.
Proof.
  reflexivity.
Qed.