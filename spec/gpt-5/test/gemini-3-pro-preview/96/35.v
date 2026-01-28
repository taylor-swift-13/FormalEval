Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <=? 1 then false
  else 
    let fix check (i : Z) (fuel : nat) :=
      match fuel with
      | O => true
      | S f =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) f
      end
    in check 2 (Z.to_nat n).

Fixpoint count_up_to_aux (i n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if i <? n then
        if is_prime i then i :: count_up_to_aux (i + 1) n fuel'
        else count_up_to_aux (i + 1) n fuel'
      else []
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux 2 n (Z.to_nat n).

Example test_count_up_to: count_up_to 11 = [2; 3; 5; 7].
Proof.
  vm_compute. reflexivity.
Qed.