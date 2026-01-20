Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
    let next_current := Z.min x (current_min + x) in
    let next_global := Z.min global_min next_current in
    minSubArraySum_aux xs next_current next_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum : minSubArraySum [5%Z; 5%Z; 5%Z; 5%Z; 5%Z; 5%Z; 5%Z] = 5%Z.
Proof. reflexivity. Qed.