
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (filtered : list string) : Prop :=
  filtered = filter (fun s => String.starts_with s prefix) strings.
