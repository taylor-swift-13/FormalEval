Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) fuel'
      end
    in check 2 (Z.to_nat n).

Fixpoint count_up_to_aux (n : Z) (curr : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if curr <? n then
      if is_prime curr then curr :: count_up_to_aux n (curr + 1) fuel'
      else count_up_to_aux n (curr + 1) fuel'
    else []
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux n 2 (Z.to_nat n).

Example test_count_up_to: count_up_to 16 = [2; 3; 5; 7; 11; 13].
Proof. reflexivity. Qed.