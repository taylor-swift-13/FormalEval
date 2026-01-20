Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr : Z) (glob : Z) : Z :=
  match nums with
  | [] => glob
  | x :: rest =>
    let curr' := Z.min x (curr + x) in
    let glob' := Z.min glob curr' in
    minSubArraySum_aux rest curr' glob'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: rest => minSubArraySum_aux rest x x
  end.

Example test_minSubArraySum: minSubArraySum [-9999999999999999] = -9999999999999999.
Proof. reflexivity. Qed.