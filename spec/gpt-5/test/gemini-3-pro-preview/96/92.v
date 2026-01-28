Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <=? 1 then false
  else
    let fix iter (i : Z) (fuel : nat) :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else iter (i + 1) fuel'
      end
    in iter 2 (Z.to_nat n).

Definition count_up_to (n : Z) : list Z :=
  let fix iter (i : Z) (fuel : nat) :=
    match fuel with
    | O => []
    | S fuel' =>
      if i >=? n then []
      else
        if is_prime i then i :: iter (i + 1) fuel'
        else iter (i + 1) fuel'
    end
  in iter 2 (Z.to_nat n).

Example test_count_up_to : count_up_to 54 = [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z; 19%Z; 23%Z; 29%Z; 31%Z; 37%Z; 41%Z; 43%Z; 47%Z; 53%Z].
Proof. reflexivity. Qed.