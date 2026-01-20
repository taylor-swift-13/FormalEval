Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint string_to_list (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c rest => (String c EmptyString) :: string_to_list rest
  end.

Definition flatten_to_chars (strings : list string) : list string :=
  flat_map string_to_list strings.

Definition filter_by_prefix_spec (strings : list string) (result : list string) : Prop :=
  result = flatten_to_chars strings.

Example test_filter_by_prefix :
  filter_by_prefix_spec ["ubu"%string; ""%string] ["u"%string; "b"%string; "u"%string].
Proof.
  unfold filter_by_prefix_spec.
  unfold flatten_to_chars.
  simpl.
  reflexivity.
Qed.