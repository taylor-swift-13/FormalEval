Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
      let new_current_min := Z.min x (current_min + x) in
      let new_global_min := Z.min global_min new_current_min in
      minSubArraySum_aux xs new_current_min new_global_min
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-10; -30; -50; 60; -70; 80; -90; 100] = -110.
Proof. reflexivity. Qed.