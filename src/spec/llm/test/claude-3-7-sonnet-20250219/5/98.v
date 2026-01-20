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
  intersperse_spec [7%nat; 3%nat; 6%nat; 8%nat; 4%nat; 2%nat; 2%nat] 10%nat 
    [7%nat; 10%nat; 3%nat; 10%nat; 6%nat; 10%nat; 8%nat; 10%nat; 4%nat; 10%nat; 2%nat; 10%nat; 2%nat].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.