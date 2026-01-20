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
  intersperse_spec [4%nat; 1%nat; 2%nat; 3%nat; 3%nat] 7
    [4%nat; 7%nat; 1%nat; 7%nat; 2%nat; 7%nat; 3%nat; 7%nat; 3%nat].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.