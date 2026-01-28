Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint kadane_step (l : list Z) (curr : Z) (glob : Z) : Z :=
  match l with
  | [] => glob
  | x :: xs =>
      let curr' := Z.max x (curr + x) in
      let glob' := Z.max glob curr' in
      kadane_step xs curr' glob'
  end.

Definition maxSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => kadane_step xs x x
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  Z.opp (maxSubArraySum (map Z.opp nums)).

Example test_minSubArraySum : minSubArraySum [-1%Z; -8%Z; 2%Z; -3%Z; 4%Z; -7%Z; 8%Z; -8%Z; 10%Z] = -13%Z.
Proof. reflexivity. Qed.