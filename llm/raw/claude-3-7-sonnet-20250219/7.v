
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Definition filter_by_substring_spec (strings : list string) (substring : string) (filtered : list string) : Prop :=
  filtered = filter (fun s => if string_included s substring then true else false) strings.
