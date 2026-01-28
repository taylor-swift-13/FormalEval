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

Example test_1234567C2...BBAA20200 :
  problem_78_spec "1234567C275322022EBDCEEFFA7F89ABCDEF002EEEFAD89073533ABCDEF12345BBAA20200" 33.
Proof.
  unfold problem_78_spec, hex_key_impl.
  simpl.

  (* We manually unfold count_prime_hex on the input string,
     evaluating is_prime_hex_digit on each char and summing 1s for primes *)

  (* Because the string is long, we perform a gradual simplification stepwise *)
  (* Use the fact that recursion unfolds by String h t *)

  (* We will rewrite the string as String h t repeatedly for clarity. *)
  remember "1234567C275322022EBDCEEFFA7F89ABCDEF002EEEFAD89073533ABCDEF12345BBAA20200" as s eqn:Hs.
  revert Hs.
  induction s as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    rewrite <- Hs.
    unfold is_prime_hex_digit.
    destruct h;
      try (simpl; f_equal; apply IH; reflexivity);
      repeat match goal with
      | _ => reflexivity
      | _ => simpl
      | _ => progress unfold is_prime_hex_digit
      | _ => progress simpl
      | _ => break_if
      end.
Abort.

(* The above attempt to unfold stepwise is verbose and impractical here.
   Instead, because count_prime_hex and is_prime_hex_digit are fully defined,
   and the input string is concrete and constant,
   the easiest is to use compute to evaluate hex_key_impl directly. *)

Example test_1234567C2...BBAA20200 :
  problem_78_spec "1234567C275322022EBDCEEFFA7F89ABCDEF002EEEFAD89073533ABCDEF12345BBAA20200" 33.
Proof.
  unfold problem_78_spec, hex_key_impl.
  compute.
  reflexivity.
Qed.