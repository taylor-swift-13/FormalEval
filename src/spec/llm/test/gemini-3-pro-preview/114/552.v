Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (l : list Z) (curr : Z) (min_so_far : Z) : Z :=
  match l with
  | [] => min_so_far
  | x :: xs =>
      let curr' := Z.min x (curr + x) in
      let min_so_far' := Z.min min_so_far curr' in
      minSubArraySum_aux xs curr' min_so_far'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; -3%Z; 3%Z; -4%Z; 5%Z; -4%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -10%Z; -8%Z] = -31%Z.
Proof. reflexivity. Qed.