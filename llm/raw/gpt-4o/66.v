
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Init.Nat.

Definition digitSum_spec (s : string) (sum : nat) : Prop :=
  sum = fold_right Nat.add 0 (map (fun ch => if (andb (Nat.leb 65 (nat_of_ascii ch)) (Nat.leb (nat_of_ascii ch) 90)) then nat_of_ascii ch else 0) (list_ascii_of_string s)).
