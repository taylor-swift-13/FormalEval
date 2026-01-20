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

Example remove_vowels_test_case :
  remove_vowels_spec
    ["x"%char; "X"%char; "C"%char; "a"%char; "a"%char; "a"%char; "a"%char; "A"%char; "E"%char; "E"%char; "E"%char; "E"%char; "!"%char; "y"%char; "Y"%char; "z"%char; "d"%char; "o"%char; "e"%char; "l"%char; "o"%char; "I"%char; "Z"%char; "d"%char; "D"%char; "L"%char; "Z"%char; "v"%char; "a"%char; "r"%char; "!"%char; "o"%char; "u"%char; "s"%char]
    ["x"%char; "X"%char; "C"%char; "!"%char; "y"%char; "Y"%char; "z"%char; "d"%char; "l"%char; "Z"%char; "d"%char; "D"%char; "L"%char; "Z"%char; "v"%char; "r"%char; "!"%char; "s"%char].
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.