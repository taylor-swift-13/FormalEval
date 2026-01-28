Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <=? 1 then false
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

Fixpoint count_up_to_aux (curr : Z) (limit : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if curr >=? limit then []
    else if is_prime curr then curr :: count_up_to_aux (curr + 1) limit fuel'
    else count_up_to_aux (curr + 1) limit fuel'
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux 2 n (Z.to_nat n).

Example test_count_up_to: count_up_to 152 = [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z; 19%Z; 23%Z; 29%Z; 31%Z; 37%Z; 41%Z; 43%Z; 47%Z; 53%Z; 59%Z; 61%Z; 67%Z; 71%Z; 73%Z; 79%Z; 83%Z; 89%Z; 97%Z; 101%Z; 103%Z; 107%Z; 109%Z; 113%Z; 127%Z; 131%Z; 137%Z; 139%Z; 149%Z; 151%Z].
Proof. reflexivity. Qed.