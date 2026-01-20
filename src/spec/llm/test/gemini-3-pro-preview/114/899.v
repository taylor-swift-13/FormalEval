Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr : Z) (glob : Z) : Z :=
  match nums with
  | [] => glob
  | x :: xs =>
      let new_curr := Z.min x (curr + x) in
      let new_glob := Z.min glob new_curr in
      minSubArraySum_aux xs new_curr new_glob
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z] = -2%Z.
Proof. reflexivity. Qed.