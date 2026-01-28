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

Example test_hex_key_long : problem_78_spec "2022E753BDC123ABB333A11DDBCBCDEF202020CBAABBB73533A11DDBC555547567CEEFAD890ABCDEF12345BBAA20201234567CEEFA7ABCDEF20ABCDEF202020CBAABBBBB333A11DDBC555520222E2020CBAABBBBB333A11DDBCACDF111188727159CEFFCEEFAD12113BCCBBD4EE11ACDF11253ABB333A11DDBCBCDEF2020200CBAAB2BB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BB3AA20200AD21753BDCEE753BDCF03BCCBBBD4ABCD2020D45B67C2022EEEFAD890ABCDEF12345BBAA20200CC22EEFFEEDDCCBBAAEFEADC55553BACDF11118872159CEEFFCEEFAD213BCCBBD4DD89073533ABCDEF12345BBBAA20200EE7711ABCD2020DDB2BCC22EEFFEEDDCCBBAA" 256.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  native_compute.
  reflexivity.
Qed.