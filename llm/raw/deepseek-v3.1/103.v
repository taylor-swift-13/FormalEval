
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Definition rounded_avg_spec (n m : nat) (result : string + Z) : Prop :=
  if n >? m then
    result = inr (-1)
  else
    exists avg : nat,
      avg = round ((n + m) / 2) /\
      result = inl ("0b" ++ (Nat.to_string avg)).
