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

Example remove_vowels_test_long :
  remove_vowels_spec 
    ["A"%char; "x"%char; "X"%char; "y"%char; "Y"%char; "w"%char; "z"%char; "Z"%char; "E"%char; "w"%char; "o"%char; "r"%char; "l"%char; "l"%char; "q"%char; "u"%char; "i"%char; "t"%char; "o"%char; "d"%char; "a"%char; "y"%char; "?"%char; "c"%char; "k"%char; "!"%char; "A"%char; "x"%char; "X"%char; "y"%char; "w"%char; "o"%char; "r"%char; "l"%char; "A"%char; "x"%char; "c"%char; "a"%char; "p"%char; "s"%char; "."%char; "x"%char; "X"%char; "y"%char; "Y"%char; "z"%char; "Z"%char; "E"%char; "o"%char; "h"%char; "e"%char; "!"%char; "!"%char; "Y"%char; "z"%char; "Z"%char; "E"%char]
    ["x"%char; "X"%char; "y"%char; "Y"%char; "w"%char; "z"%char; "Z"%char; "w"%char; "r"%char; "l"%char; "l"%char; "q"%char; "t"%char; "d"%char; "y"%char; "?"%char; "c"%char; "k"%char; "!"%char; "x"%char; "X"%char; "y"%char; "w"%char; "r"%char; "l"%char; "x"%char; "c"%char; "p"%char; "s"%char; "."%char; "x"%char; "X"%char; "y"%char; "Y"%char; "z"%char; "Z"%char; "h"%char; "!"%char; "!"%char; "Y"%char; "z"%char; "Z"%char].
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.