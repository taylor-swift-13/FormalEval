Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (meh : Z) (msf : Z) : Z :=
  match nums with
  | [] => msf
  | x :: xs =>
      let meh' := Z.min x (meh + x) in
      let msf' := Z.min msf meh' in
      minSubArraySum_aux xs meh' msf'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example minSubArraySum_example : minSubArraySum [-5; -8; -3; -2; -3; 6; -3; -1] = -21.
Proof. reflexivity. Qed.