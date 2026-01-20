Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Open Scope string_scope.
Open Scope bool_scope.

Definition is_vowel_char (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition is_y (c : ascii) : bool :=
  match c with
  | "y"%char | "Y"%char => true
  | _ => false
  end.

Fixpoint vowels_count_func (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
    let rest_count := vowels_count_func s' in
    if is_vowel_char c then
      1 + rest_count
    else if (is_y c) && (s' =? EmptyString) then
      1 + rest_count
    else
      rest_count
  end.

Definition vowels_count_spec (s : string) (count : nat) : Prop :=
  count = vowels_count_func s.

Example vowels_count_test_psiaeaeiiobcdfghjcetioiusneasbstemiousnessaeiasbstemiousnessaeiouyfaceftiousnessouyfaceaOAEIOUYXfazcetioubcdffghjklAEIOUYXWmnpqrstvwxyzsnnessWouyfsnessssioouyyc :
  vowels_count_spec "psiaeaeiiobcdfghjcetioiusneasbstemiousnessaeiasbstemiousnessaeiouyfaceftiousnessouyfaceaOAEIOUYXfazcetioubcdffghjklAEIOUYXWmnpqrstvwxyzsnnessWouyfsnessssioouyyc" 69.
Proof.
  unfold vowels_count_spec.
  simpl.
  reflexivity.
Qed.