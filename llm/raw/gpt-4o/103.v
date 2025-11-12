
Require Import ZArith.
Require Import String.

Definition rounded_avg_spec (n m : Z) (result : string + Z) : Prop :=
  (n > m -> result = inr (-1)) /\
  (n <= m -> let avg := Z.div (n + m + 1) 2 in result = inl ("0b" ++ Z.to_binary avg)).
