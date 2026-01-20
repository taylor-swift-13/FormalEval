
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Fixpoint starts_with (s prefix : string) : bool :=
  match prefix, s with
  | EmptyString, _ => true
  | String c1 p1, String c2 s2 =>
      if ascii_dec c1 c2 then starts_with s2 p1 else false
  | _, _ => false
  end.

Definition how_many_times_spec (string substring : string) (count : nat) : Prop :=
  count = length (filter (fun i =>
    starts_with (skipn i (list_of_string string)) substring) (seq 0 (String.length string))).

