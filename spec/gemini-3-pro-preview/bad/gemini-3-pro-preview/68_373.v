Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
    let aux := fix aux (rem : list Z) (idx : nat) (min_val : Z) (min_idx : nat) {struct rem} : list Z :=
      match rem with
      | [] => [min_val; Z.of_nat min_idx]
      | x :: xs =>
        if x <? min_val
        then aux xs (S idx) x idx
        else aux xs (S idx) min_val min_idx
      end
    in aux t 1%nat h 0%nat
  end.

Example test_case: solve [10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 0%Z] = [0%Z; 62%Z].
Proof. reflexivity. Qed.