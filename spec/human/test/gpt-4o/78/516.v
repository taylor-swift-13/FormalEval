Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char
  | "B"%char | "D"%char => true
  | _ => false
  end.

Fixpoint count_prime_hex (s : string) : nat :=
  match s with
  | "" => 0
  | String h t =>
    (if is_prime_hex_digit h then 1 else 0) +
    count_prime_hex t
  end.

Definition hex_key_impl (s : string) : nat :=
  count_prime_hex s.

Definition problem_78_pre (s : string) : Prop := True.

Definition problem_78_spec (s : string) (output : nat) : Prop :=
  output = hex_key_impl s.

Example test_case_1 : problem_78_spec "11ABCD22020DDBB12345B67C2022EEEFAD890ABAB4CDEF202020CBAABBBDDDDDDCCCCC111112345B67C1BB333AB4CDEF202020CBAABBB5DDDDDDCCCCC111112212345B67CEEFAD890ABCDEF12345BB35AA2020033CEEEF753BDCEEFAD2020123456789ABCDEABCDEF202020CBAABBBDDDDDDCCCCC1111122222333334444455555F0EAED44444555555A113DDBC2001221234275322022EBDCEEFFBA7F89ABCDEF0025B67CEEFAD890ABCDEF12345BBAA2020033444555555CDEF12345BBBBAA" 185.
Proof.
  unfold problem_78_spec, hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  reflexivity.
Qed.