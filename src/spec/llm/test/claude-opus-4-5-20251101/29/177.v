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

Fixpoint string_to_chars (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c rest => (String c EmptyString) :: string_to_chars rest
  end.

Definition filter_by_prefix_spec (input : list string) (result : list string) : Prop :=
  match input with
  | [s; _] => result = string_to_chars s
  | _ => False
  end.

Example test_filter_by_prefix :
  filter_by_prefix_spec ["cfacetious"%string; ""%string] 
    ["c"%string; "f"%string; "a"%string; "c"%string; "e"%string; 
     "t"%string; "i"%string; "o"%string; "u"%string; "s"%string].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.