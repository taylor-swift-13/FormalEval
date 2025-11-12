
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.

Open Scope R_scope.

Definition truncate_number_spec (number decimal_part : R) : Prop :=
  number > 0 /\
  let int_part := IZR (Zfloor number) in
  decimal_part = number - int_part /\
  0 <= decimal_part < 1.
