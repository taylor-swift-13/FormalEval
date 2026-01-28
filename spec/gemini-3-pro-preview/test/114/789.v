Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr : Z) (glob : Z) : Z :=
  match nums with
  | [] => glob
  | n :: ns =>
      let curr' := Z.min n (curr + n) in
      let glob' := Z.min glob curr' in
      minSubArraySum_aux ns curr' glob'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns => minSubArraySum_aux ns n n
  end.

Example test_minSubArraySum_new : minSubArraySum [-1%Z; 2%Z; -3%Z; 4%Z; -5%Z; 6%Z; -7%Z; 8%Z; -9%Z; 10%Z; 8%Z] = -9%Z.
Proof. reflexivity. Qed.