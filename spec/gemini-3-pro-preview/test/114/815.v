Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
    let current_min' := Z.min x (current_min + x) in
    let global_min' := Z.min global_min current_min' in
    minSubArraySum_aux xs current_min' global_min'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-10%Z; -9%Z; -7%Z; -6%Z; -5%Z; -4%Z; -3%Z; -9%Z; -2%Z; -1%Z] = -56%Z.
Proof. reflexivity. Qed.