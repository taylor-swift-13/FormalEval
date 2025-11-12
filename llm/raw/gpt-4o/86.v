
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.Ascii.

Definition anti_shuffle_spec (s : string) (result : string) : Prop :=
  let words := String.split " " s in
  let ordered_words := map (fun w => String.concat "" (List.sort (fun ch1 ch2 => Nat.ltb (Nat.of_ascii ch1) (Nat.of_ascii ch2)) (String.list_ascii w))) words in
  result = String.concat " " ordered_words.
