
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Definition count_upper_spec (s : string) (cnt : nat) : Prop :=
  cnt = fold_left (fun acc i =>
                     if (Nat.even i && existsb (fun c => c =? nth i (list_of_string s) " ") (list_of_string "AEIOU"))%bool
                     then acc + 1
                     else acc)
                  (seq 0 (String.length s)) 0.
