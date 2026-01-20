
Require Import ZArith.
Require Import String.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition closest_integer_spec (value : string) (closest : Z) : Prop :=
  exists val : Z,
    (exists frac : Q,
      Qeq (Qmake (Z.of_nat (nat_of_ascii (hd "0" (explode value)))) 1) (val + frac) /\
      (frac <> 0.5)).
