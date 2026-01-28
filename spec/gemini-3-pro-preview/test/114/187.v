Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
      let fix iter (l : list Z) (current_min : Z) (global_min : Z) : Z :=
        match l with
        | [] => global_min
        | x :: xs =>
            let current_min' := Z.min x (current_min + x) in
            let global_min' := Z.min global_min current_min' in
            iter xs current_min' global_min'
        end
      in iter ns n n
  end.

Example test_minSubArraySum: minSubArraySum [1; -1; 1; -1; 1; -1; 1; -1; 1; -1; -1] = -2.
Proof.
  reflexivity.
Qed.