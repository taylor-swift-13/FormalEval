Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Fixpoint filter_string (f : ascii -> bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if f c then String c (filter_string f s') else filter_string f s'
  end.

Definition problem_51_pre (input : string) : Prop := True.

Definition problem_51_spec (input : string) (output : string) : Prop :=
  output = filter_string (fun c => negb (is_vowel c)) input.

Example test_remove_vowels_long :
  problem_51_spec "Thisa iProgThise ence haaei:oumming is fun1234567890This sentence has vowels: aeious a Testi!" "Ths PrgThs nc h:mmng s fn1234567890Ths sntnc hs vwls: s  Tst!".
Proof.
  unfold problem_51_spec.
  simpl.
  reflexivity.
Qed.