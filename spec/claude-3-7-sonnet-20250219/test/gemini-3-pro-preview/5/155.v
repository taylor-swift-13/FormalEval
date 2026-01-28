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

Example test_intersperse : intersperse_spec [1; 2; -9; 4; 4] 0 [1; 0; 2; 0; -9; 0; 4; 0; 4].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.