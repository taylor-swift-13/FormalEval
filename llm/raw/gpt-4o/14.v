
Require Import List String.

Definition all_prefixes_spec (string : string) (prefixes : list string) : Prop :=
  prefixes = map (fun i => substring 0 (i + 1) string) (seq 0 (String.length string)).
