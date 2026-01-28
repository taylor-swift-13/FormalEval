Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

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

Example problem_78_test_nat : problem_78_spec "CE73ABB333A11DDBCBCDEF202011ACD2753BDCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0020DDBB12345B67C2022EEEFAD890ABCDE12345B67C2022EEEFAD890ABCFDEF275373ABB3033A11DDBCBCDEF202020CBAABBB2BB333CA11D0DBC5555EF002AB4CDEF202020CBAABBBDDDDDDCCCCC111112212345B67CEEFAD890ABCDEF12345BBAA2020033444555555E12345BBAA20200F12345BBBBAA20CBAABBB2BB333CA11DDEFEAD" 171.
Proof.
  unfold problem_78_spec, hex_key_impl.
  simpl.
  reflexivity.
Qed.

Example problem_78_test_Z : Z.of_nat (hex_key_impl "CE73ABB333A11DDBCBCDEF202011ACD2753BDCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0020DDBB12345B67C2022EEEFAD890ABCDE12345B67C2022EEEFAD890ABCFDEF275373ABB3033A11DDBCBCDEF202020CBAABBB2BB333CA11D0DBC5555EF002AB4CDEF202020CBAABBBDDDDDDCCCCC111112212345B67CEEFAD890ABCDEF12345BBAA2020033444555555E12345BBAA20200F12345BBBBAA20CBAABBB2BB333CA11DDEFEAD") = 171%Z.
Proof.
  unfold hex_key_impl.
  simpl.
  reflexivity.
Qed.