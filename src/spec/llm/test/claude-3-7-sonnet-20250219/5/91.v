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

Example test_intersperse_spec_negatives:
  intersperse_spec [-4; -4; 6; 5; 1; 9] 2 [-4; 2; -4; 2; 6; 2; 5; 2; 1; 2; 9].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.