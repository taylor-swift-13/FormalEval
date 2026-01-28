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

Example test_intersperse_1 : intersperse_spec [15; 63; 2; -2; 5; -93; 100; 5; -9] 9 [15; 9; 63; 9; 2; 9; -2; 9; 5; 9; -93; 9; 100; 9; 5; 9; -9].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.