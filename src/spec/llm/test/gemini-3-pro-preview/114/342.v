Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix iter (l : list Z) (curr : Z) (min_val : Z) : Z :=
      match l with
      | [] => min_val
      | x :: xs =>
        let curr' := Z.min x (curr + x) in
        let min_val' := Z.min min_val curr' in
        iter xs curr' min_val'
      end
    in iter ns n n
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 30%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -1%Z.
Proof. reflexivity. Qed.