Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let new_current_min := Z.min x (current_min + x) in
      let new_min_so_far := Z.min min_so_far new_current_min in
      minSubArraySum_aux xs new_current_min new_min_so_far
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_case_1: minSubArraySum [-8%Z; -1%Z; 2%Z; -3%Z; 4%Z; 6%Z; -7%Z; -9%Z] = -16%Z.
Proof. reflexivity. Qed.