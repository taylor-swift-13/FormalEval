Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
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

Example check : minSubArraySum [1%Z; 99%Z; 1%Z; -1%Z; 100%Z; -1%Z; 1%Z; -7%Z; -9%Z; -1%Z; 1%Z; -1%Z] = -17%Z.
Proof. reflexivity. Qed.