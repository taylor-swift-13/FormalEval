Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix aux (l : list Z) (current_min global_min : Z) : Z :=
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

Example test_minSubArraySum : minSubArraySum [-20; 30; -40; 50; 1; 70; -80; 50; 90; 10; -20] = -80.
Proof. reflexivity. Qed.