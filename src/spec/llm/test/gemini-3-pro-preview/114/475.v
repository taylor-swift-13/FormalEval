Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_min_so_far := Z.min min_so_far new_current in
      minSubArraySum_aux xs new_current new_min_so_far
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum_1:
  minSubArraySum [-100%Z; 9%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; -51%Z; 100%Z; -100%Z; -50%Z] = -100251%Z.
Proof. reflexivity. Qed.