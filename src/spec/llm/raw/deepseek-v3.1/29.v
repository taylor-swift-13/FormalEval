
Require Import List.
Require Import String.
Require Import Basics.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (result : list string) : Prop :=
  result = filter (fun s => prefix_dec s prefix) strings.

Definition prefix_dec (s : string) (prefix : string) : bool :=
  if prefix_string s prefix then true else false.
