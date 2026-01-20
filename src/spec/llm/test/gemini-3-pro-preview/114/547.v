Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix aux (l : list Z) (curr : Z) (glob : Z) : Z :=
      match l with
      | [] => glob
      | x :: xs =>
        let curr' := Z.min x (curr + x) in
        let glob' := Z.min glob curr' in
        aux xs curr' glob'
      end
    in aux ns n n
  end.

Example test_minSubArraySum: minSubArraySum [-1%Z; -2%Z; -4%Z; 5%Z; -6%Z; 7%Z; 1%Z; 4%Z; 4%Z; 1%Z; 6%Z; 2%Z; -1%Z; -6%Z; 7%Z; 5%Z] = -8%Z.
Proof. reflexivity. Qed.