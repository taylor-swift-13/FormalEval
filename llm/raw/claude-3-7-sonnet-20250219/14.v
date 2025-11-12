
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition all_prefixes_spec (string : string) (prefixes : list string) : Prop :=
  prefixes = map (fun i => substring 0 (S i) string) (seq 0 (String.length string)).
