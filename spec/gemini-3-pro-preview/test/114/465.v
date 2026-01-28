Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix iter (l : list Z) (curr : Z) (glob : Z) : Z :=
        match l with
        | [] => glob
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let glob' := Z.min glob curr' in
            iter ys curr' glob'
        end
      in iter xs x x
  end.

Example check : min_sub_array_sum [-3%Z; -2%Z; 3%Z; -4%Z; 5%Z; 50%Z; 7%Z; -8%Z; -10%Z; 7%Z] = -18%Z.
Proof.
  reflexivity.
Qed.