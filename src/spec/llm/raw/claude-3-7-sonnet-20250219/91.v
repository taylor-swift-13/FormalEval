
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_bored_spec (S : string) (count : nat) : Prop :=
  let replaced := String.replace "?" "." S in
  let replaced := String.replace "!" "." replaced in
  let sentences := map (fun s => String.trim s) (String.split "." replaced) in
  count = length (filter (fun s => String.startsWith s "I ") sentences).
