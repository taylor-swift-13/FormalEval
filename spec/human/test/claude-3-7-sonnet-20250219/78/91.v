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

Example test_D6747767ABCD237777A74776B7ABCD237774D23 : problem_78_spec "D6747767ABCD237777A74776B7ABCD237774D23" 28.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold count_prime_hex.

  (* manual step-by-step unfolding and evaluation of is_prime_hex_digit for each char *)
  repeat match goal with
  | |- context[String ?h ?t] =>
    let c := eval compute in (is_prime_hex_digit h) in
    cbv beta delta [is_prime_hex_digit] in c;
    let n := match c with
      | true => constr:(1)
      | false => constr:(0)
      end in
    change (count_prime_hex (String h t)) with (n + count_prime_hex t)
  end.

  (* Unfold the string step by step and sum the counts *)
  (* Due to the long string, we can evaluate in Coq *)

  (* Using compute to evaluate the whole function on the string *)
  compute.

  (* The expected result is 28 *)
  reflexivity.
Qed.