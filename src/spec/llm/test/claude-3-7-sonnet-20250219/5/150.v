Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition intersperse_spec (numbers : list Z) (delimiter : Z) (res : list Z) : Prop :=
  res = match numbers with
        | [] => []
        | x :: xs =>
          let fix aux l :=
            match l with
            | [] => []
            | y :: [] => [y]
            | y :: ys => y :: delimiter :: aux ys
            end
          in aux numbers
        end.

Example test_intersperse_spec:
  intersperse_spec [-1; 1; -2; -2; -3] 10000 
    [-1; 10000; 1; 10000; -2; 10000; -2; 10000; -3].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.