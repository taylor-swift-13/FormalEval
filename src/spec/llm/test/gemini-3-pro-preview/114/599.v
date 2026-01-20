Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix aux (l : list Z) (curr : Z) (glob : Z) : Z :=
    match l with
    | [] => glob
    | x :: xs =>
      let curr' := Z.min x (curr + x) in
      let glob' := Z.min glob curr' in
      aux xs curr' glob'
    end in
  match nums with
  | [] => 0
  | x :: xs => aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [0; -1; 1; -1; 1; 1; -100; -1; 2; -50; 1; -1; -3; -1; -50] = -203.
Proof. reflexivity. Qed.