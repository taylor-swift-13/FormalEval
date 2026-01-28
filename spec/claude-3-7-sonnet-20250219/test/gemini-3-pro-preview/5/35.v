Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
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

Example test_intersperse : intersperse_spec [7; 3; 6; 8; 4; 2; 1] (-1) [7; -1; 3; -1; 6; -1; 8; -1; 4; -1; 2; -1; 1].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.