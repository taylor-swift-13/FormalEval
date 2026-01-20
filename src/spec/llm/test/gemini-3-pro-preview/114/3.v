Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let curr_min' := Z.min x (curr_min + x) in
      let min_so_far' := Z.min min_so_far curr_min' in
      minSubArraySum_aux xs curr_min' min_so_far'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example minSubArraySum_example : minSubArraySum [-1%Z; -2%Z; -3%Z; 2%Z; -10%Z] = -14%Z.
Proof.
  reflexivity.
Qed.