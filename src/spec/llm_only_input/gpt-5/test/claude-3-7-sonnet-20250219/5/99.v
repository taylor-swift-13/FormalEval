Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Fixpoint intersperse_with (delimeter : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | [y] => [y]
  | y :: ys => y :: delimeter :: intersperse_with delimeter ys
  end.

Definition intersperse_spec (numbers : list Z) (delimeter : Z) (res : list Z) : Prop :=
  res = match numbers with
        | [] => []
        | _ => intersperse_with delimeter numbers
        end.

Example intersperse_spec_test_case :
  intersperse_spec
    [5%Z; 15%Z; 63%Z; 2%Z; -2%Z; 5%Z; 9%Z; 100%Z; 5%Z; -9%Z; 100%Z]
    8%Z
    [5%Z; 8%Z; 15%Z; 8%Z; 63%Z; 8%Z; 2%Z; 8%Z; -2%Z; 8%Z; 5%Z; 8%Z; 9%Z; 8%Z; 100%Z; 8%Z; 5%Z; 8%Z; -9%Z; 8%Z; 100%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.