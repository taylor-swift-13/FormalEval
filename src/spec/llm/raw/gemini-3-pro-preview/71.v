
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_stdlib.
Require Import Coq.ZArith.ZArith.
Open Scope R_scope.

Definition triangle_area_spec (a b c res : R) : Prop :=
  let invalid := a + b <= c \/ a + c <= b \/ b + c <= a in
  (invalid -> res = -1) /\
  (~invalid ->
    let p := (a + b + c) / 2 in
    let val := sqrt (p * (p - a) * (p - b) * (p - c)) in
    res = IZR (Z_near (val * 100)) / 100).
