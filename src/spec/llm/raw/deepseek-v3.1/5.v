
Require Import List.
Import ListNotations.

Definition intersperse_spec (numbers : list Z) (delimeter : Z) (result : list Z) : Prop :=
  match numbers with
  | [] => result = []
  | h :: t => result = h :: fold_right (fun x acc => delimeter :: x :: acc) [] t
  end.
