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

Example test_big : problem_78_spec "753BDCEACDF12345B67C2022EEEFAD890ABCDEF12345BBAA202001111887215E753BD9CEFF23BC337312345B67CEEFAD890ABCDEF12345BBAA20200CBBD431BDCF0" 60.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  repeat match goal with
  | [ |- context[String ?c ?t] ] =>
    simpl;
    unfold is_prime_hex_digit;
    simpl;
    progress (
      match c with
      | "2"%char => idtac
      | "3"%char => idtac
      | "5"%char => idtac
      | "7"%char => idtac
      | "B"%char => idtac
      | "D"%char => idtac
      | _ => idtac
      end
    )
  end.
  reflexivity.
Qed.