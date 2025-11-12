
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Definition filter_by_substring_spec (strings : list string) (substring : string) (result : list string) : Prop :=
  forall s, In s result <-> In s strings /\ String.contains s substring = true.
