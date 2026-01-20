Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

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
    "1a2b3c4d5e6fzAxXyYzZE7gcaps.8h9i10jklmnopqrstuvwxyzzzazzzzaaaquickaAAAABBBCCCdddDEEEE!" 
    "12b3c4d56fzxXyYzZ7gcps.8h910jklmnpqrstvwxyzzzzzzzqckBBBCCCdddD!".
Proof.
  unfold remove_vowels_spec.
  reflexivity.
Qed.