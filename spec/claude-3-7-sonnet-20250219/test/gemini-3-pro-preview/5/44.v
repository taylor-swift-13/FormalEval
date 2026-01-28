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

Example test_intersperse : intersperse_spec [3; 6; 2; 5; 1; 9] 1 [3; 1; 6; 1; 2; 1; 5; 1; 1; 1; 9].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.