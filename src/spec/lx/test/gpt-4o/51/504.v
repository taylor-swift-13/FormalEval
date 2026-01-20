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

Example remove_vowels_test_large :
  remove_vowels_spec
    ["y"%char; "Y"%char; "z"%char; "A"%char; "T"%char; "h"%char; "!"%char; "s"%char; " "%char; "1"%char; "s"%char; " "%char; "@"%char; " "%char; "s"%char; "t"%char; "s"%char; "r"%char; "!"%char; "n"%char; "g"%char; " "%char; "A"%char; "x"%char; "Z"%char; "X"%char; "y"%char; "Y"%char; "z"%char; "Z"%char; "b"%char; "r"%char; "a"%char; "a"%char; "a"%char; "a"%char; "A"%char; "A"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "C"%char; "C"%char; "C"%char; "d"%char; "d"%char; "d"%char; "D"%char; "a"%char; "E"%char; "E"%char; "E"%char; "E"%char; "!"%char; "o"%char; "w"%char; "n"%char; "E"%char; "w"%char; "!"%char; "t"%char; "h"%char; " "%char; "n"%char; "u"%char; "m"%char; "b"%char; "3"%char; "r"%char; "s"%char; ","%char; " "%char; "p"%char; "u"%char; "n"%char; "c"%char; "t"%char; "u"%char; "a"%char; "t"%char; "!"%char; "o"%char; "n"%char; ","%char; " "%char; "Z"%char; "b"%char; "r"%char; "a"%char; "a"%char; "a"%char; "a"%char; "A"%char; "A"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "C"%char; "C"%char; "C"%char; "d"%char; "d"%char; "d"%char; "D"%char; "a"%char; "E"%char; "E"%char; "E"%char; "E"%char; "!"%char; "o"%char; "w"%char; "n"%char; "E"%char]
    ["y"%char; "Y"%char; "z"%char; "T"%char; "h"%char; "!"%char; "s"%char; " "%char; "1"%char; "s"%char; " "%char; "@"%char; " "%char; "s"%char; "t"%char; "s"%char; "r"%char; "!"%char; "n"%char; "g"%char; " "%char; "x"%char; "Z"%char; "X"%char; "y"%char; "Y"%char; "z"%char; "Z"%char; "b"%char; "r"%char; "B"%char; "B"%char; "B"%char; "C"%char; "C"%char; "C"%char; "d"%char; "d"%char; "d"%char; "D"%char; "!"%char; "w"%char; "n"%char; "w"%char; "!"%char; "t"%char; "h"%char; " "%char; "n"%char; "m"%char; "b"%char; "3"%char; "r"%char; "s"%char; ","%char; " "%char; "p"%char; "n"%char; "c"%char; "t"%char; "t"%char; "!"%char; "n"%char; ","%char; " "%char; "Z"%char; "b"%char; "r"%char; "B"%char; "B"%char; "B"%char; "C"%char; "C"%char; "C"%char; "d"%char; "d"%char; "d"%char; "D"%char; "!"%char; "w"%char; "n"%char].
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.