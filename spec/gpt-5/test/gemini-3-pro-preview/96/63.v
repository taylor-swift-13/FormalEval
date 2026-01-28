Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) fuel'
      end
    in check 2 (Z.to_nat n).

Fixpoint count_up_to_aux (n : Z) (current : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if current <? n then
        if is_prime current then
          current :: count_up_to_aux n (current + 1) fuel'
        else
          count_up_to_aux n (current + 1) fuel'
      else []
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux n 2 (Z.to_nat n).

Example test_case_1 : count_up_to 73 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71].
Proof. reflexivity. Qed.