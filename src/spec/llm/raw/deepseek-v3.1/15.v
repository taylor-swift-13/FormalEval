
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition string_sequence_spec (n : Z) (result : string) : Prop :=
  result = (String.concat " " (map Z.to_string (seqZ 0 (Z.to_nat (n + 1))))).
