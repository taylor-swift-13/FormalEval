Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Example test_minSubArraySum: minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; 100%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100000%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z; -50%Z] = (-100101)%Z.
Proof. reflexivity. Qed.