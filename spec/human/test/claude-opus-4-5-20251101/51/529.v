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

Example test_remove_vowels_long : problem_51_spec "mFjX1wd!aAAAABBBCCCdddDEEEE!dJWPBmmta2b3cd4d5e6fz7g8h9i10jklmnopqrstuvwxyzzzzzzzaaaHello wd!aAAAABBBCCCdddDEEEE!dJWPBmmt" "mFjX1wd!BBBCCCdddD!dJWPBmmt2b3cd4d56fz7g8h910jklmnpqrstvwxyzzzzzzzHll wd!BBBCCCdddD!dJWPBmmt".
Proof.
  unfold problem_51_spec.
  simpl.
  reflexivity.
Qed.