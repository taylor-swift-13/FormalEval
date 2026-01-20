Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint string_to_chars (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c rest => (String c EmptyString) :: string_to_chars rest
  end.

Fixpoint flat_map_chars (strings : list string) : list string :=
  match strings with
  | [] => []
  | s :: rest => string_to_chars s ++ flat_map_chars rest
  end.

Definition filter_by_prefix_spec (strings : list string) (result : list string) : Prop :=
  result = flat_map_chars strings.

Example test_filter_by_prefix :
  filter_by_prefix_spec ["cfacus"%string; ""%string] ["c"%string; "f"%string; "a"%string; "c"%string; "u"%string; "s"%string].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.