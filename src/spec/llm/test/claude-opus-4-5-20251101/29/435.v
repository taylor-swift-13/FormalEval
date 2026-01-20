Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint starts_with (prefix s : string) : bool :=
  match prefix, s with
  | EmptyString, _ => true
  | String c1 rest1, String c2 rest2 =>
      if Ascii.eqb c1 c2 then starts_with rest1 rest2 else false
  | String _ _, EmptyString => false
  end.

Fixpoint string_to_char_strings (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c rest => (String c EmptyString) :: string_to_char_strings rest
  end.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (result : list string) : Prop :=
  result = flat_map string_to_char_strings (filter (fun s => negb (String.eqb s EmptyString)) strings).

Example test_filter_by_prefix :
  filter_by_prefix_spec ["qwqe"%string; ""%string] ""%string ["q"%string; "w"%string; "q"%string; "e"%string].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.