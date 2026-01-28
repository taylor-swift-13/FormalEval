Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
    let current_min' := Z.min x (current_min + x) in
    let min_so_far' := Z.min min_so_far current_min' in
    minSubArraySum_aux xs current_min' min_so_far'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [-3%Z; -2%Z; 3%Z; -4%Z; -4%Z; 5%Z; 50%Z; 7%Z; -8%Z; -50000%Z; -10%Z; 7%Z] = -50018%Z.
Proof.
  reflexivity.
Qed.