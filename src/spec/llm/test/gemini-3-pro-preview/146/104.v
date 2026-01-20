Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero (operations : list Z) : Z :=
  let fix aux (ops : list Z) (balance : Z) : bool :=
    match ops with
    | [] => false
    | op :: rest => 
      let new_balance := balance + op in
      if new_balance <? 0 then true else aux rest new_balance
    end in
  if aux operations 0 then 0 else 1.

Example test_case : below_zero [39; 240] = 1.
Proof. reflexivity. Qed.