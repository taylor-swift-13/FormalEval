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
        else if n mod i =? 0 then false
        else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Fixpoint range (start : Z) (len : nat) : list Z :=
  match len with
  | O => []
  | S len' => start :: range (start + 1) len'
  end.

Definition count_up_to (n : Z) : list Z :=
  if n <=? 2 then []
  else filter is_prime (range 2 (Z.to_nat (n - 2))).

Example test_case: count_up_to 47 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43].
Proof. reflexivity. Qed.