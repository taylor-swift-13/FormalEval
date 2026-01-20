
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Definition how_many_times_spec (string substring : string) (occurences : nat) : Prop :=
  occurences = fold_left (fun acc i =>
                            if substring_dec substring (substring i (String.length substring) string)
                            then acc + 1
                            else acc)
                          (seq 0 (String.length string)) 0.
