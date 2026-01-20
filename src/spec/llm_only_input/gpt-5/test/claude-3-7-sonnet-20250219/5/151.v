Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition intersperse_spec (numbers : list Z) (delimeter : Z) (res : list Z) : Prop :=
  res = match numbers with
        | [] => []
        | x :: xs =>
          let fix aux (l : list Z) : list Z :=
            match l with
            | [] => []
            | y :: [] => [y]
            | y :: ys => y :: delimeter :: aux ys
            end
          in aux numbers
        end.

Example intersperse_spec_test_case :
  intersperse_spec [-22%Z; 1%Z; 2%Z; 18%Z; 1%Z] 5%Z [-22%Z; 5%Z; 1%Z; 5%Z; 2%Z; 5%Z; 18%Z; 5%Z; 1%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.