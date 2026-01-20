Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition program (nums : list Z) : Z :=
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

Example test_case: program [100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; -10%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; -50000%Z] = -150010%Z.
Proof. reflexivity. Qed.