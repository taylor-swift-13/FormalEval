Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition remove_vowels_spec (input : string) (output : string) : Prop :=
  output = string_of_list_ascii (filter (fun c => negb (is_vowel c)) (list_ascii_of_string input)).

Example remove_vowels_test_case :
  remove_vowels_spec "thvvayYZzZ!ouse" "thvvyYZzZ!s".
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.