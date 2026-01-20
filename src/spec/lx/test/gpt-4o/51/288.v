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
  remove_vowels_spec ["1"%char; "a"%char; "2"%char; "b"%char; "3"%char; "c"%char; "4"%char; "d"%char; "5"%char; "e"%char; "6"%char; "f"%char; "z"%char; "7"%char; "g"%char; "8"%char; "h"%char; "9"%char; "i"%char; "1"%char; "0"%char; "j"%char; "k"%char; "l"%char; "d"%char; "o"%char; "e"%char; "l"%char; "o"%char; "I"%char; "Z"%char; "d"%char; "D"%char; "L"%char; "x"%char; "y"%char; "z"%char; "z"%char; "z"%char; "z"%char; "z"%char; "z"%char; "a"%char; "a"%char; "a"%char; "H"%char; "e"%char; "l"%char; "l"%char; "o"%char]
                     ["1"%char; "2"%char; "b"%char; "3"%char; "c"%char; "4"%char; "d"%char; "5"%char; "6"%char; "f"%char; "z"%char; "7"%char; "g"%char; "8"%char; "h"%char; "9"%char; "1"%char; "0"%char; "j"%char; "k"%char; "l"%char; "d"%char; "l"%char; "Z"%char; "d"%char; "D"%char; "L"%char; "x"%char; "y"%char; "z"%char; "z"%char; "z"%char; "z"%char; "z"%char; "z"%char; "H"%char; "l"%char; "l"%char].
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.