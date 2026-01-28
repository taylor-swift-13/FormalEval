Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
  minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 100%Z; 99%Z; -100%Z; 50%Z; -50%Z; 100%Z; 9%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z; -100%Z] = -100101%Z.
Proof. reflexivity. Qed.