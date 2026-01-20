Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_sum : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let current_sum := current_sum + x in
      let min_so_far := Z.min min_so_far current_sum in
      let current_sum := if current_sum >? 0 then 0 else current_sum in
      minSubArraySum_aux xs current_sum min_so_far
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux nums 0 x
  end.

Example test_minSubArraySum:
  minSubArraySum [2; 1; -1; 1; 1; -1; 1; -1; 1; -1; -1; 1; -1; 1; -1] = -2.
Proof.
  reflexivity.
Qed.