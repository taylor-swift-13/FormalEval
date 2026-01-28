Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix aux (l : list Z) (curr_min : Z) (global_min : Z) : Z :=
    match l with
    | [] => global_min
    | x :: xs =>
        let curr_min' := Z.min x (curr_min + x) in
        let global_min' := Z.min global_min curr_min' in
        aux xs curr_min' global_min'
    end in
  match nums with
  | [] => 0
  | x :: xs => aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-100%Z; -10%Z; -60%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; -100%Z; 99%Z; -100%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z; -50%Z] = -100372%Z.
Proof. reflexivity. Qed.