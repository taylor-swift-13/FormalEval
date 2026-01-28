Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (l : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match l with
  | [] => min_so_far
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min min_so_far new_current in
      minSubArraySum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-100; 50; -50; 100; 50; -50; 100; -100; -50; 100; -100; 50; -50; 100; -100; 50; -51; 100; -100] = -151.
Proof. reflexivity. Qed.