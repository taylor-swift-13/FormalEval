Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (fuel : nat) (i : Z) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
          if i * i >? n then true
          else if (n mod i) =? 0 then false
          else check fuel' (i + 1)
      end
    in check (Z.to_nat n) 2.

Definition count_up_to (n : Z) : list Z :=
  filter is_prime (map Z.of_nat (seq 0 (Z.to_nat n))).

Example test_case: count_up_to 10 = [2; 3; 5; 7].
Proof. reflexivity. Qed.