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

Example problem_51_test_case_new :
  problem_51_pre "123456789The quick e the This sentence has 3vowels: aeioulazy dog.0" /\
  problem_51_spec "123456789The quick e the This sentence has 3vowels: aeioulazy dog.0" "123456789Th qck  th Ths sntnc hs 3vwls: lzy dg.0".
Proof.
  split.
  - unfold problem_51_pre. exact I.
  - unfold problem_51_spec. compute. reflexivity.
Qed.