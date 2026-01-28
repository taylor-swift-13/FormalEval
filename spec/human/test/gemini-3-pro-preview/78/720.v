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

Example test_hex_key_complex : problem_78_spec "1ACDF11118872159CEFF23BCCBBD423456711ABCD20D20753BDCEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBBAA20200DDBBBCFFEEDDCCBBAA890ABCEADCDEFA12345BBAA20200" 64.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  reflexivity.
Qed.