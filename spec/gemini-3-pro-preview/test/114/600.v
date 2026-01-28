Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (l : list Z) (meh : Z) (msf : Z) : Z :=
  match l with
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

Example test_minSubArraySum: minSubArraySum [1; 99; 1; -1; 1; -1; 1; -9; -1; 1; -2; -1] = -12.
Proof. reflexivity. Qed.