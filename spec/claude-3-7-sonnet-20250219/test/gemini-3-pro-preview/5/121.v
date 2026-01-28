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

Example test_intersperse_basic : intersperse_spec [4; 1; 2; 3; 3] 7 [4; 7; 1; 7; 2; 7; 3; 7; 3].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.