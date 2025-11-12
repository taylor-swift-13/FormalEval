
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Definition is_bored_spec (S : string) (boredoms : nat) : Prop :=
  let delimiters := ["."] in
  let sentences := map (fun x => String.trim x) (String.split delimiters ((String.replace "?" "." (String.replace "!" "." S)))) in
  boredoms = length (filter (fun s => String.prefix "I " s) sentences).
