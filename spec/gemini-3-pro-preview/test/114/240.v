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

Example minSubArraySum_example_new :
  minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; 1%Z; -50%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -150%Z.
Proof. reflexivity. Qed.