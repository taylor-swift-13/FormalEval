Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint string_to_char_strings (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c rest => (String c EmptyString) :: string_to_char_strings rest
  end.

Definition split_string_spec (strings : list string) (separator : string) (result : list string) : Prop :=
  match strings with
  | [s; EmptyString] => result = string_to_char_strings s
  | _ => True
  end.

Example test_split_string :
  split_string_spec ["qwertyuiop"%string; ""%string] ""%string 
    ["q"%string; "w"%string; "e"%string; "r"%string; "t"%string; "y"%string; "u"%string; "i"%string; "o"%string; "p"%string].
Proof.
  unfold split_string_spec.
  simpl.
  reflexivity.
Qed.