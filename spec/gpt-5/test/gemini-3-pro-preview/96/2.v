Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false else
  let fix check (i : Z) (fuel : nat) : bool :=
    match fuel with
    | O => true
    | S fuel' =>
      if i * i >? n then true
      else if n mod i =? 0 then false
      else check (i + 1) fuel'
    end
  in check 2 (Z.to_nat n).

Fixpoint count_up_to_aux (i : Z) (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if i >=? n then []
    else
      if is_prime i then i :: count_up_to_aux (i + 1) n fuel'
      else count_up_to_aux (i + 1) n fuel'
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux 2 n (Z.to_nat n).

Example test_case_1: count_up_to 6 = [2; 3; 5].
Proof.
  reflexivity.
Qed.