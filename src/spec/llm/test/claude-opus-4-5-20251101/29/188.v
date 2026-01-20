Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint string_to_chars (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c rest => (String c EmptyString) :: string_to_chars rest
  end.

Definition filter_by_prefix_spec (strings : list string) (result : list string) : Prop :=
  result = flat_map string_to_chars strings.

Example test_filter_by_prefix :
  filter_by_prefix_spec ["filmbu"%string; ""%string] ["f"%string; "i"%string; "l"%string; "m"%string; "b"%string; "u"%string].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.