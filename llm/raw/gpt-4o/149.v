
Require Import List.
Require Import String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition cmp (s t : string) : comparison :=
  match Nat.compare (String.length s) (String.length t) with
  | Eq => String.compare s t
  | Lt => Lt
  | Gt => Gt
  end.

Definition filter_even_length (lst : list string) : list string :=
  filter (fun s => Nat.even (String.length s)) lst.

Definition sorted_list_sum_spec (lst : list string) (result : list string) : Prop :=
  result = sort cmp (filter_even_length lst).
