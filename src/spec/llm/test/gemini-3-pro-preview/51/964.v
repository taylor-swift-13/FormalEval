Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(* Define the conversion functions which are not in the standard library *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: (list_ascii_of_string s')
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

Definition is_vowel (c : ascii) : bool :=
  existsb (fun v => Ascii.eqb c v) ["a"; "e"; "i"; "o"; "u"; "A"; "E"; "I"; "O"; "U"].

Definition remove_vowels_spec (text : string) (result : string) : Prop :=
  result = string_of_list_ascii (filter (fun c => negb (is_vowel c)) (list_ascii_of_string text)).

Example test_remove_vowels_complex : 
  remove_vowels_spec 
    ("Th!s 1s @ str!ngl w!th numb3rs, puncotuat!oHellon, and var!ous caayoubcd" ++ String (ascii_of_nat 10) (String (ascii_of_nat 10) (String (ascii_of_nat 10) (String (ascii_of_nat 10) "efghijklmnopqrstuvwxy!zTh!s 1s @ str!ngl w!th numb3rs, punctuat!oHellon, aar!ous caps.ps."))))
    ("Th!s 1s @ str!ngl w!th nmb3rs, pnctt!Hlln, nd vr!s cybcd" ++ String (ascii_of_nat 10) (String (ascii_of_nat 10) (String (ascii_of_nat 10) (String (ascii_of_nat 10) "fghjklmnpqrstvwxy!zTh!s 1s @ str!ngl w!th nmb3rs, pnctt!Hlln, r!s cps.ps.")))).
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.