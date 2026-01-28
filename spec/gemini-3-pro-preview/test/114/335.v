Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
    match l with
    | [] => global_min
    | x :: xs =>
      let new_current_min := Z.min x (current_min + x) in
      let new_global_min := Z.min global_min new_current_min in
      aux xs new_current_min new_global_min
    end in
  match nums with
  | [] => 0
  | x :: xs => aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -99%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; 100%Z; -100%Z; 9%Z; -50%Z; 50001%Z; 100%Z; 50%Z] = -141%Z.
Proof. reflexivity. Qed.