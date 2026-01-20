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
    end
  in
  match nums with
  | [] => 0
  | x :: xs => aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-10; -9; -8; -7; -5; -60; -3; -9; -2; 30; -5] = -113.
Proof. reflexivity. Qed.