Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
  match l with
  | [] => global_min
  | x :: xs =>
      let next_current := Z.min x (current_min + x) in
      let next_global := Z.min global_min next_current in
      minSubArraySum_aux xs next_current next_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; 1%Z; 6%Z; 1%Z; -1%Z; -6%Z] = -8%Z.
Proof.
  simpl.
  reflexivity.
Qed.