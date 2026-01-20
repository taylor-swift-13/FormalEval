Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix loop (l : list Z) (current_min : Z) (global_min : Z) : Z :=
      match l with
      | [] => global_min
      | x :: xs =>
        let current_min' := Z.min x (current_min + x) in
        let global_min' := Z.min global_min current_min' in
        loop xs current_min' global_min'
      end
    in loop ns n n
  end.

Example test_case_1 : minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -50%Z; -99%Z; 100%Z; 60%Z; 99%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z; 99%Z] = -100101%Z.
Proof. reflexivity. Qed.