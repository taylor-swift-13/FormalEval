Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Local Open Scope string_scope.

Definition is_separator (c : ascii) : bool :=
  orb (Ascii.eqb c " "%char) 
      (orb (Ascii.eqb c ","%char) (Ascii.eqb c (Ascii.ascii_of_nat 10))).

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
    ("sMulti" ++ String (ascii_of_nat 10) 
      ("line" ++ String (ascii_of_nat 10) 
        ("string" ++ String (ascii_of_nat 10) 
          ("Hello," ++ String (ascii_of_nat 10) 
            ("meaningemoving,world!" ++ String (ascii_of_nat 10) "paceno")))))
    ["sMulti"; "line"; "string"; "Hello"; "meaningemoving"; "world!"; "paceno"].
Proof.
  unfold words_string_spec.
  reflexivity.
Qed.