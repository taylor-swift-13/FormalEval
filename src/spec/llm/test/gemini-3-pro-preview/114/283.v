Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min min_so_far new_current in
      minSubArraySum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; 99%Z; 1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -9%Z; -1%Z; 1%Z; -1%Z] = -11%Z.
Proof.
  reflexivity.
Qed.