Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Definition starts_with (p s : string) : Prop :=
  exists t, s = String.append p t.

Inductive filter_rel (p : string -> Prop) : list string -> list string -> Prop :=
| filter_rel_nil : filter_rel p [] []
| filter_rel_cons_keep x xs ys :
    p x ->
    filter_rel p xs ys ->
    filter_rel p (x :: xs) (x :: ys)
| filter_rel_cons_drop x xs ys :
    ~ p x ->
    filter_rel p xs ys ->
    filter_rel p (x :: xs) ys.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (out : list string) : Prop :=
  filter_rel (starts_with prefix) strings out.