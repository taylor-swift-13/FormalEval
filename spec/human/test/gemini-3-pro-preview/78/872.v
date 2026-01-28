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

Example test_hex_key_large : problem_78_spec "753BDCEEFAD2020121721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BBB3137D1DDBB31CBAA202002E345BBAAA200456789C11ABCD2020DDB1ACDF11118872159CEFF23BCCBBD423456711ABCD2020753BDDDBBBCFFEEDDCCBBAA890ABCDEFA12345BBAA20200BCC22EBB3137D1DDBB31CEFFEEDDCCBBAADEF0" 124.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  reflexivity.
Qed.