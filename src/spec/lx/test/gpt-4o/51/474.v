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
    ["1"%char; "a"%char; "m"%char; "n"%char; "o"%char; "p"%char; "q"%char; "r"%char; "s"%char; "t"%char; "u"%char; "v"%char; "w"%char; "x"%char; "y"%char; "z"%char; "z"%char; "z"%char; "z"%char; "a"%char; "a"%char; "a"%char; "q"%char; "u"%char; "i"%char; "c"%char; "k"%char; "a"%char; "A"%char; "A"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "C"%char; "C"%char; "C"%char; "d"%char; "d"%char; "d"%char; "D"%char; "E"%char; "E"%char; "E"%char; "E"%char; "!"%char]
    ["1"%char; "m"%char; "n"%char; "p"%char; "q"%char; "r"%char; "s"%char; "t"%char; "v"%char; "w"%char; "x"%char; "y"%char; "z"%char; "z"%char; "z"%char; "z"%char; "q"%char; "c"%char; "k"%char; "B"%char; "B"%char; "B"%char; "C"%char; "C"%char; "C"%char; "d"%char; "d"%char; "d"%char; "D"%char; "!"%char].
Proof.
  unfold remove_vowels_spec.
  reflexivity.
Qed.