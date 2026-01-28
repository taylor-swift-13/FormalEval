Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let current_min' := Z.min x (current_min + x) in
      let min_so_far' := Z.min min_so_far current_min' in
      minSubArraySum_aux xs current_min' min_so_far'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [100000%Z; -50000%Z; 50000%Z; -100000%Z; -9%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; -50001%Z; 50000%Z; 99999%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; -100000%Z] = -200010%Z.
Proof. reflexivity. Qed.