Require Import Coq.Lists.List.
Import ListNotations.

Definition intersperse_spec (numbers : list nat) (delimeter : nat) (res : list nat) : Prop :=
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

Example test_intersperse_basic : intersperse_spec [7; 3; 6; 8; 4; 2; 1] 10 [7; 10; 3; 10; 6; 10; 8; 10; 4; 10; 2; 10; 1].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.