Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Local Open Scope string_scope.

Definition is_separator (c : ascii) : bool :=
  orb (Ascii.eqb c " "%char) 
      (orb (Ascii.eqb c ","%char) 
           (Ascii.eqb c (Ascii.ascii_of_nat 10))).

Fixpoint words_string_aux (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => 
      if String.eqb acc "" then [] else [acc]
  | String c s' =>
      if is_separator c then
        if String.eqb acc "" then words_string_aux s' ""
        else acc :: words_string_aux s' ""
      else
        words_string_aux s' (acc ++ String c EmptyString)
  end.

Definition words_string_spec (s : string) (result : list string) : Prop :=
  result = words_string_aux s "".

Example test_words_string :
  words_string_spec 
    "Two spaces after,  one spaces beforfe  , and no saces in beMulti
line
string
Hwords,
tween"
    ["Two"; "spaces"; "after"; "one"; "spaces"; "beforfe"; "and"; "no"; "saces"; "in"; "beMulti"; "line"; "string"; "Hwords"; "tween"].
Proof.
  unfold words_string_spec.
  reflexivity.
Qed.