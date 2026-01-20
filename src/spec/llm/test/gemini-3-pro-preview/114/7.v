Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix aux (l : list Z) (current_min global_min : Z) : Z :=
    match l with
    | [] => global_min
    | x :: xs =>
      let current_min' := Z.min x (current_min + x) in
      let global_min' := Z.min global_min current_min' in
      aux xs current_min' global_min'
    end in
  match nums with
  | [] => 0
  | x :: xs => aux xs x x
  end.

Example test_minSubArraySum : minSubArraySum [100%Z; -1%Z; -2%Z; -3%Z; 10%Z; -5%Z] = -6%Z.
Proof. reflexivity. Qed.