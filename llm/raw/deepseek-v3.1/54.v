
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sets.MoreSets.

Definition same_chars_spec (s0 : string) (s1 : string) : Prop :=
  set_eq (list_to_set (list_of_ascii s0)) (list_to_set (list_of_ascii s1)).
