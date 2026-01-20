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

Example remove_vowels_test_jumpseThe :
  remove_vowels_spec
    ["j"%char; "u"%char; "m"%char; "p"%char; "s"%char; "e"%char; "T"%char; "h"%char; "e"%char]
    ["j"%char; "m"%char; "p"%char; "s"%char; "T"%char; "h"%char].
Proof.
  unfold remove_vowels_spec.
  simpl.
  reflexivity.
Qed.