Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
    match l with
    | [] => global_min
    | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min global_min new_current in
      aux xs new_current new_global
    end in
  match nums with
  | [] => 0
  | x :: xs => aux xs x x
  end.

Example test_minSubArraySum_1 : minSubArraySum [-1; 2; -3; 4; -5; 6; -7; 8; -7; -9; 10; -7; 4; 10] = -16.
Proof. reflexivity. Qed.