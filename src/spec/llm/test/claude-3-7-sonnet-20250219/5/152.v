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

Example test_intersperse_spec_case:
  intersperse_spec [3; 248; 3; 4; 248] 48 [3; 48; 248; 48; 3; 48; 4; 48; 248].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.