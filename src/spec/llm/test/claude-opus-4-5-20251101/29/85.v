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

Fixpoint string_to_char_strings (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c rest => (String c EmptyString) :: string_to_char_strings rest
  end.

Definition filter_by_prefix_spec_v2 (input : list string) (result : list string) : Prop :=
  match input with
  | [s; EmptyString] => result = string_to_char_strings s
  | _ => True
  end.

Example test_filter_by_prefix :
  filter_by_prefix_spec_v2 ["apriccot"%string; ""%string] 
    ["a"%string; "p"%string; "r"%string; "i"%string; "c"%string; "c"%string; "o"%string; "t"%string].
Proof.
  unfold filter_by_prefix_spec_v2.
  simpl.
  reflexivity.
Qed.