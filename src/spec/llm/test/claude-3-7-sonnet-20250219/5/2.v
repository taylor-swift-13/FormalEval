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

Example test_intersperse_spec:
  intersperse_spec [5; 6; 3; 2] 8 [5; 8; 6; 8; 3; 8; 2].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.