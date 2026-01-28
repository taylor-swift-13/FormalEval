Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (glob : Z) : Z :=
      match l with
      | [] => glob
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let glob' := Z.min glob curr' in
        aux ys curr' glob'
      end
    in aux xs x x
  end.

Example test_case:
  min_sub_array_sum [ -100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -50%Z; 100%Z; 60%Z; 99%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z ] = -100101%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.