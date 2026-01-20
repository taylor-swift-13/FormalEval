Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
      let fix iter (l : list Z) (curr min_so_far : Z) : Z :=
        match l with
        | [] => min_so_far
        | x :: xs =>
            let curr' := Z.min x (curr + x) in
            let min_so_far' := Z.min min_so_far curr' in
            iter xs curr' min_so_far'
        end
      in iter ns n n
  end.

Example test_minSubArraySum: minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; -90%Z; -50%Z; -100%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; -51%Z; 101%Z; 100%Z; 100%Z] = -100351%Z.
Proof. reflexivity. Qed.