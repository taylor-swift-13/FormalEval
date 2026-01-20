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

Example remove_vowels_test_complex :
  remove_vowels_spec
    ["t"%char; ","%char; "!"%char; "h"%char; "o"%char; "i"%char; "H"%char; "e"%char; "l"%char; "l"%char; "o"%char; "n"%char; ","%char; "l"%char; "d"%char; "d"%char; "!"%char; "l"%char; "i"%char; "o"%char; "u"%char; "q"%char]
    ["t"%char; ","%char; "!"%char; "h"%char; "H"%char; "l"%char; "l"%char; "n"%char; ","%char; "l"%char; "d"%char; "d"%char; "!"%char; "l"%char; "q"%char].
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.