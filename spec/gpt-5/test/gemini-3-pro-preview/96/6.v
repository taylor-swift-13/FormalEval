Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix aux (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Fixpoint count_up_to_aux (curr : Z) (limit : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if curr <? limit then
      if is_prime curr then curr :: count_up_to_aux (curr + 1) limit fuel'
      else count_up_to_aux (curr + 1) limit fuel'
    else []
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux 2 n (Z.to_nat n).

Example test_count_up_to: count_up_to 22%Z = [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z; 19%Z].
Proof. reflexivity. Qed.