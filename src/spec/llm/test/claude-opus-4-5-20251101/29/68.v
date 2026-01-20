Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint starts_with (prefix s : string) : bool :=
  match prefix, s with
  | EmptyString, _ => true
  | String c1 rest1, String c2 rest2 =>
      if Ascii.eqb c1 c2 then starts_with rest1 rest2 else false
  | String _ _, EmptyString => false
  end.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (result : list string) : Prop :=
  result = filter (fun s => starts_with prefix s) strings.

Fixpoint string_to_char_list (s : string) : list Ascii.ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_char_list rest
  end.

Fixpoint char_list_to_strings (chars : list Ascii.ascii) : list string :=
  map (fun c => String c EmptyString) chars.

Definition select_by_prefix_spec (input : string) (prefix : string) (result : list string) : Prop :=
  result = char_list_to_strings (filter (fun c => starts_with prefix (String c EmptyString)) (string_to_char_list input)).

Example test_select_by_prefix :
  select_by_prefix_spec "hhh"%string "h"%string ["h"%string; "h"%string; "h"%string].
Proof.
  unfold select_by_prefix_spec.
  unfold char_list_to_strings.
  unfold string_to_char_list.
  simpl.
  reflexivity.
Qed.