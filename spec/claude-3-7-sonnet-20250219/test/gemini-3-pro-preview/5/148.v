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

Example test_intersperse_1 : intersperse_spec [3; 2; 3; 4; 3] 19 [3; 19; 2; 19; 3; 19; 4; 19; 3].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.