Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr : Z) (glob : Z) : Z :=
  match nums with
  | [] => glob
  | x :: xs =>
      let curr' := Z.min x (curr + x) in
      let glob' := Z.min glob curr' in
      minSubArraySum_aux xs curr' glob'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; 0%Z; 1%Z; -1%Z; 90%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; -70%Z; -1%Z; -101%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 0%Z; 1%Z; -1%Z] = -174%Z.
Proof. reflexivity. Qed.