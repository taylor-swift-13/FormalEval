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

Definition count_up_to (n : Z) : list Z :=
  filter is_prime (map Z.of_nat (seq 0 (Z.to_nat n))).

Example test_count_up_to: count_up_to 94 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89].
Proof. reflexivity. Qed.