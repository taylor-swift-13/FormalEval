Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr : Z) (min_s : Z) : Z :=
  match nums with
  | [] => min_s
  | x :: xs =>
      let curr' := Z.min x (curr + x) in
      let min_s' := Z.min min_s curr' in
      minSubArraySum_aux xs curr' min_s'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [1; 3; 2; -3; 7; -6; 8; -10; 1; 1] = -10.
Proof.
  reflexivity.
Qed.