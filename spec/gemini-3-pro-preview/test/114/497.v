Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) : Z * Z :=
  match nums with
  | [] => (0, 0)
  | [x] => (x, x)
  | x :: xs =>
      let (min_s, min_g) := minSubArraySum_aux xs in
      let current_min_s := Z.min x (x + min_s) in
      let current_min_g := Z.min current_min_s min_g in
      (current_min_s, current_min_g)
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  snd (minSubArraySum_aux nums).

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 30%Z; -1%Z; 1%Z; -1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 60%Z; 1%Z] = -3%Z.
Proof. reflexivity. Qed.