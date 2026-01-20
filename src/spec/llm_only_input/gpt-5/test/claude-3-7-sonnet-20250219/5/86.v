Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition intersperse_spec (numbers : list Z) (delimeter : Z) (res : list Z) : Prop :=
  res = match numbers with
        | [] => []
        | x :: xs => 
          let fix aux l :=
            match l with
            | [] => []
            | y :: [] => [y]
            | y :: ys => y :: delimeter :: aux ys
            end
          in aux numbers
        end.

Example intersperse_spec_test_case :
  intersperse_spec [7%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] (-4%Z)
                   [7%Z; -4%Z; 1%Z; -4%Z; 1%Z; -4%Z; 1%Z; -4%Z; 1%Z; -4%Z; 1%Z; -4%Z; 1%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.