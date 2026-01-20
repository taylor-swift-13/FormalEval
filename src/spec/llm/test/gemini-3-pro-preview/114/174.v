Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix aux (l : list Z) (curr : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | x :: xs =>
        let curr' := Z.min x (curr + x) in
        let min_so_far' := Z.min min_so_far curr' in
        aux xs curr' min_so_far'
      end
    in aux ns n n
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -101%Z.
Proof. reflexivity. Qed.