
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.
Open Scope Z_scope.

Definition closest_integer_spec (value : string) (result : Z) : Prop :=
  exists r, (r = Raux.string_to_R value) /\
  let lower := IZR (Z.floor r) in
  let upper := IZR (Z.ceil r) in
  let diff_lower := Rabs (r - lower) in
  let diff_upper := Rabs (upper - r) in
  if Rlt_dec diff_lower diff_upper then result = Z.floor r
  else if Rgt_dec diff_lower diff_upper then result = Z.ceil r
  else
    (if Rle_dec r 0 then result = Z.floor r - 1
     else result = Z.floor r + 1).
