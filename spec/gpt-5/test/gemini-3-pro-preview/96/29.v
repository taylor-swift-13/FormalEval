Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S f =>
          if i * i >? n then true
          else if n mod i =? 0 then false
          else check (i + 1) f
      end
    in check 2 (Z.to_nat n).

Fixpoint count_up_to_aux (i n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S f =>
      if i <? n then
        if is_prime i then i :: count_up_to_aux (i + 1) n f
        else count_up_to_aux (i + 1) n f
      else []
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux 2 n (Z.to_nat n).

Example test_count_up_to: count_up_to 31 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29].
Proof. reflexivity. Qed.