Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint intersperse_fun (numbers : list Z) (delimeter : Z) : list Z :=
  match numbers with
  | [] => []
  | [x] => [x]
  | x :: y :: tl => x :: delimeter :: intersperse_fun (y :: tl) delimeter
  end.

Definition intersperse_spec (numbers : list Z) (delimeter : Z) (res : list Z) : Prop :=
  res = intersperse_fun numbers delimeter.