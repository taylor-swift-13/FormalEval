Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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

Example test_minSubArraySum: minSubArraySum [1; -2; 3; 9; -4; 5; 9; -2; -10] = -12.
Proof. reflexivity. Qed.