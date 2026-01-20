Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint min_subarray_sum_aux (curr : Z) (glob : Z) (l : list Z) : Z :=
  match l with
  | [] => glob
  | x :: xs =>
      let curr' := Z.min x (curr + x) in
      let glob' := Z.min glob curr' in
      min_subarray_sum_aux curr' glob' xs
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_subarray_sum_aux x x xs
  end.

Example test_minSubArraySum: minSubArraySum [61%Z; 10%Z; -20%Z; 30%Z; -40%Z; 50%Z; 70%Z; -7%Z; 60%Z; 90%Z; -100%Z; 10%Z] = -100%Z.
Proof. reflexivity. Qed.