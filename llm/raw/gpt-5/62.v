Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition derivative_spec (xs : list Z) (ys : list Z) : Prop :=
  forall i,
    nth_error ys i =
    match nth_error xs (S i) with
    | Some xi => Some (xi * Z.of_nat (S i))
    | None => None
    end.