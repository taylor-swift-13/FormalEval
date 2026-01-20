
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

Definition total_chars (l : list string) : nat :=
  fold_right (fun s acc => length s + acc) 0 l.

Definition total_match_spec (lst1 lst2 result : list string) : Prop :=
  let c1 := total_chars lst1 in
  let c2 := total_chars lst2 in
  (c1 <= c2 -> result = lst1) /\
  (c1 > c2 -> result = lst2).
