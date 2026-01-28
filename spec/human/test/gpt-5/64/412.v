Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Arith.Arith Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Open Scope string_scope.

Definition is_vowel_char (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char
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
    let rest := vowels_count_func s' in
    if is_vowel_char c then
      1 + rest
    else
      if (is_y c) && (s' =? EmptyString) then
        1 + rest
      else
        rest
  end.

Definition vowels_count_impl (s : string) : nat :=
  vowels_count_func s.

Definition problem_64_pre (s : string) : Prop := True.

Definition problem_64_spec (s : string) (output : nat) : Prop :=
  output = vowels_count_impl s.

Example problem_64_test_long_nat :
  problem_64_spec "heBLBaAAaaAaaAaaiaeaeiouyfacetiousnessioouyaaabcdfghjklmnpqrstvwcpsbcdfghjklmnpabstemiousnessqrstvwxyzologyxyz" 41.
Proof.
  unfold problem_64_spec, vowels_count_impl.
  simpl.
  reflexivity.
Qed.

Example problem_64_test_long_Z :
  Z.of_nat (vowels_count_impl "heBLBaAAaaAaaAaaiaeaeiouyfacetiousnessioouyaaabcdfghjklmnpqrstvwcpsbcdfghjklmnpabstemiousnessqrstvwxyzologyxyz") = 41%Z.
Proof.
  simpl.
  reflexivity.
Qed.