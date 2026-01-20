Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
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

Example test_minSubArraySum:
  minSubArraySum [-10; -30; -30; 40; -50; 60; -70; 81; -90; 100] = -99.
Proof. reflexivity. Qed.