Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

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

Example intersperse_spec_test_nonempty :
  intersperse_spec
    [Z.to_nat 1%Z; Z.to_nat 1%Z; Z.to_nat 2%Z; Z.to_nat 2%Z; Z.to_nat 3%Z; Z.to_nat 3%Z]
    (Z.to_nat 4%Z)
    [Z.to_nat 1%Z; Z.to_nat 4%Z; Z.to_nat 1%Z; Z.to_nat 4%Z; Z.to_nat 2%Z; Z.to_nat 4%Z; Z.to_nat 2%Z; Z.to_nat 4%Z; Z.to_nat 3%Z; Z.to_nat 4%Z; Z.to_nat 3%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.