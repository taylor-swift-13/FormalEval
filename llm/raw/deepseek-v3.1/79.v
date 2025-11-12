
Require Import String.
Require Import ZArith.

Definition decimal_to_binary_spec (decimal : Z) (result : string) : Prop :=
  result = "db" ++ (StringOfZ decimal 2) ++ "db".
