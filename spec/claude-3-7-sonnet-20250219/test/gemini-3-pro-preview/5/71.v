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

Example test_intersperse_complex : intersperse_spec [6; 3; 7; 5; 1; 9; 3] 7 [6; 7; 3; 7; 7; 7; 5; 7; 1; 7; 9; 7; 3].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.