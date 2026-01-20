Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
  match l with
  | [] => global_min
  | x :: xs =>
    let new_current := Z.min x (current_min + x) in
    let new_global := Z.min global_min new_current in
    minSubArraySum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -7%Z; -99%Z; -100%Z; 9%Z; 7%Z] = -206%Z.
Proof.
  compute.
  reflexivity.
Qed.