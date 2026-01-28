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

Example problem_78_test_nat : problem_78_spec "1721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BCEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1234567890ABCDEF12345BBAA20200BBCD21234567890ABCDEFA12345BBAA20200DBBCC22EECEAAA202002E345BBAAA200" 87.
Proof.
  unfold problem_78_spec, hex_key_impl.
  simpl.
  reflexivity.
Qed.

Example problem_78_test_Z : Z.of_nat (hex_key_impl "1721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BCEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1234567890ABCDEF12345BBAA20200BBCD21234567890ABCDEFA12345BBAA20200DBBCC22EECEAAA202002E345BBAAA200") = 87%Z.
Proof.
  unfold hex_key_impl.
  simpl.
  reflexivity.
Qed.