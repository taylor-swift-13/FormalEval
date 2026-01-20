Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition remove_vowels_spec (input : list ascii) (output : list ascii) : Prop :=
  output = filter (fun c => negb (is_vowel c)) input.

Example remove_vowels_test_tokday :
  remove_vowels_spec
    (["t"; "o"; "k"; "d"; "a"; "y"; "?"; "j"; "k"; "l"; "m"; "n"; "o"; "p"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"; "z"; "z"; "t"; "z"; "z"; "z"; "z"; "z"]%char)
    (["t"; "k"; "d"; "y"; "?"; "j"; "k"; "l"; "m"; "n"; "p"; "r"; "s"; "t"; "v"; "w"; "x"; "y"; "z"; "z"; "z"; "t"; "z"; "z"; "z"; "z"; "z"]%char).
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.