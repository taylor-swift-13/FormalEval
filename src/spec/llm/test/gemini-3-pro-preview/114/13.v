Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
      match l with
      | [] => global_min
      | x :: xs =>
        let current_min' := Z.min x (current_min + x) in
        let global_min' := Z.min global_min current_min' in
        aux xs current_min' global_min'
      end
    in aux ns n n
  end.

Example test_minSubArraySum : minSubArraySum [2; 4; -1; 3; 5; -4; 1; -2] = -5.
Proof.
  reflexivity.
Qed.