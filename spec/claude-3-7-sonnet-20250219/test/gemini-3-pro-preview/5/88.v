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

Example test_intersperse_1 : intersperse_spec [3; 6; 5; 1; 9; 6; 1] 10001 [3; 10001; 6; 10001; 5; 10001; 1; 10001; 9; 10001; 6; 10001; 1].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.