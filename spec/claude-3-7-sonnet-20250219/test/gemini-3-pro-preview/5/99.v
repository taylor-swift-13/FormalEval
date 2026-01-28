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

Example test_intersperse_1 : intersperse_spec [5; 15; 63; 2; -2; 5; 9; 100; 5; -9; 100] 8 [5; 8; 15; 8; 63; 8; 2; 8; -2; 8; 5; 8; 9; 8; 100; 8; 5; 8; -9; 8; 100].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.