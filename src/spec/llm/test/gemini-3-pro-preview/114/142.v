Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
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

Example test_minSubArraySum: minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z] = -100211%Z.
Proof. reflexivity. Qed.