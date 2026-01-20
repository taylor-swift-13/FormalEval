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

Example remove_vowels_test_non_empty :
  remove_vowels_spec 
    (["i"; " "; "a"; "m"; " "; "1"; "2"; "3"; "1"; "4"; "0"; "u"; "s"; "i"; "n"; "g"; " "; "p"; "y"; "t"; "h"; "o"; "n"]%char)
    ([" "; "m"; " "; "1"; "2"; "3"; "1"; "4"; "0"; "s"; "n"; "g"; " "; "p"; "y"; "t"; "h"; "n"]%char).
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.