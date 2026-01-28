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

Example test_intersperse_1 : intersperse_spec [-4; -4; 6; 5; 1; 9] 1 [-4; 1; -4; 1; 6; 1; 5; 1; 1; 1; 9].
Proof.
  unfold intersperse_spec.
  reflexivity.
Qed.