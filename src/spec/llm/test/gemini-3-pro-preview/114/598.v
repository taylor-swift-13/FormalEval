Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: tl =>
    let current_min' := Z.min x (current_min + x) in
    let global_min' := Z.min global_min current_min' in
    minSubArraySum_aux tl current_min' global_min'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: tl => minSubArraySum_aux tl x x
  end.

Example test_minSubArraySum: minSubArraySum [-1; -8; 2; -3; 4; -5; 6; 5; -4; -4; -7; -8; 8; 10; 8] = -23.
Proof. reflexivity. Qed.