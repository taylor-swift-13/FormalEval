Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let new_curr_min := Z.min x (curr_min + x) in
      let new_min_so_far := Z.min min_so_far new_curr_min in
      minSubArraySum_aux xs new_curr_min new_min_so_far
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [3%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; -8%Z; -1%Z; 9%Z; -2%Z; 4%Z; -10%Z] = -15%Z.
Proof. reflexivity. Qed.