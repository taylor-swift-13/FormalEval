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

Example test_hex_key_complex : problem_78_spec "1ACDF11118872159CEFF23BCCBBDDDBBCFFEEDDCCBBBAA20200DDBBBCCACEADEA12345CEA753BDD67891234567890ABCDEF121234567890ABCDEF12345BBAA2202E345BBAA2202E0ABCDEF12345BBAA2202EFFEEDDCCBBAA890ABCEAD0CDEFA12345BBAA20200CEEF" 89.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  reflexivity.
Qed.