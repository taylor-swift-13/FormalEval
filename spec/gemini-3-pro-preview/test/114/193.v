Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
      let fix scan (l : list Z) (current_min : Z) (global_min : Z) : Z :=
        match l with
        | [] => global_min
        | x :: xs =>
            let next_min := Z.min x (current_min + x) in
            scan xs next_min (Z.min global_min next_min)
        end
      in scan ns n n
  end.

Example test_case_1: minSubArraySum [-1; 1; -1; 1; -1; 1; -1; 0; 1; -1; 1; -1; 1; -1; 1; -1; 30; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; 1] = -1.
Proof. reflexivity. Qed.