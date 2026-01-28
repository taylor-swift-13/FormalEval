Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_kadane (l : list Z) (curr : Z) (glob : Z) : Z :=
  match l with
  | [] => glob
  | x :: xs =>
      let curr' := Z.min x (curr + x) in
      let glob' := Z.min glob curr' in
      min_kadane xs curr' glob'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_kadane xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; 3%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; 4%Z; 1%Z; 6%Z; 7%Z; 2%Z; -1%Z; -6%Z] = -8%Z.
Proof. reflexivity. Qed.