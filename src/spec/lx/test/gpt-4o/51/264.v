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

Example remove_vowels_test :
  remove_vowels_spec ["t"%char; "w"%char; "o"%char; "r"%char; "l"%char; "A"%char; "c"%char; "a"%char; "p"%char; "s"%char; "."%char; "x"%char; "X"%char; "y"%char; "y"%char; "Y"%char; "z"%char; "Z"%char; "E"%char; "h"%char; "e"%char; "!"%char; "!"%char; "h"%char; "h"%char; "h"%char; "e"%char] 
  ["t"%char; "w"%char; "r"%char; "l"%char; "c"%char; "p"%char; "s"%char; "."%char; "x"%char; "X"%char; "y"%char; "y"%char; "Y"%char; "z"%char; "Z"%char; "h"%char; "!"%char; "!"%char; "h"%char; "h"%char; "h"%char].
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.