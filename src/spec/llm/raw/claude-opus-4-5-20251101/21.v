
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.

Definition list_min (l : list R) : R :=
  fold_right Rmin (hd 0 l) (tl l).

Definition list_max (l : list R) : R :=
  fold_right Rmax (hd 0 l) (tl l).

Definition rescale_to_unit_spec (numbers : list R) (result : list R) : Prop :=
  length numbers >= 2%nat /\
  let mi := list_min numbers in
  let ma := list_max numbers in
  let k := 1 / (ma - mi) in
  ma <> mi /\
  length result = length numbers /\
  (forall i, (i < length numbers)%nat ->
    nth i result 0 = (nth i numbers 0 - mi) * k) /\
  (forall r, In r result -> 0 <= r <= 1) /\
  In 0 result /\
  In 1 result.
