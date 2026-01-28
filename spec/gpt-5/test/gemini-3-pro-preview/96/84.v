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
      | S f =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) f
      end
    in check 2 (Z.to_nat n).

Fixpoint range (start : Z) (len : nat) : list Z :=
  match len with
  | O => []
  | S len' => start :: range (start + 1) len'
  end.

Definition count_up_to (n : Z) : list Z :=
  filter is_prime (range 0 (Z.to_nat n)).

Example test_count_up_to: count_up_to 108 = [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z; 19%Z; 23%Z; 29%Z; 31%Z; 37%Z; 41%Z; 43%Z; 47%Z; 53%Z; 59%Z; 61%Z; 67%Z; 71%Z; 73%Z; 79%Z; 83%Z; 89%Z; 97%Z; 101%Z; 103%Z; 107%Z].
Proof. reflexivity. Qed.