Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix helper (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => false
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else helper (i + 1) fuel'
      end
    in helper 2 (Z.to_nat n).

Fixpoint count_up_to_loop (i : Z) (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if i >=? n then []
    else if is_prime i then i :: count_up_to_loop (i + 1) n fuel'
    else count_up_to_loop (i + 1) n fuel'
  end.

Definition count_up_to (n : Z) : list Z :=
  if n <=? 2 then []
  else count_up_to_loop 2 n (Z.to_nat n).

Example test_count_up_to: count_up_to 12 = [2; 3; 5; 7; 11].
Proof. reflexivity. Qed.