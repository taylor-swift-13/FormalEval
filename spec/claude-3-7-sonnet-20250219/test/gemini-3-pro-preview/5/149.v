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

Example test_intersperse_1 : intersperse_spec [10; -2; 5; 10; -5; 2; 10] (-9) [10; -9; -2; -9; 5; -9; 10; -9; -5; -9; 2; -9; 10].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.