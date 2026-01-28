Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix iter (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S f =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else iter (i + 1) f
      end
    in iter 2 (Z.to_nat n).

Fixpoint count_up_to_aux (n : Z) (i : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S f =>
      if i <? n then
        if is_prime i then i :: count_up_to_aux n (i + 1) f
        else count_up_to_aux n (i + 1) f
      else []
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux n 2 (Z.to_nat (n + 1)).

Example test_count_up_to: count_up_to 107 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101; 103].
Proof. reflexivity. Qed.