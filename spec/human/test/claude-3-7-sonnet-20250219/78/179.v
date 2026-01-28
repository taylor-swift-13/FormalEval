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

Example test_long : problem_78_spec "11ACD2020DDBB12345B67C2022EEEFAD890ABCDEF12345BBBBAA" 25.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '1' 0 *)
  simpl. (* '1' 0 sum=0 *)
  unfold is_prime_hex_digit.
  simpl. (* 'A' 0 sum=0 *)
  simpl. (* 'C' 0 sum=0 *)
  unfold is_prime_hex_digit.
  simpl. (* 'D' 1 sum=1 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '2' 1 sum=2 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '0' 0 sum=2 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '2' 1 sum=3 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '0' 0 sum=3 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'D' 1 sum=4 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'D' 1 sum=5 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'B' 1 sum=6 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'B' 1 sum=7 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '1' 0 sum=7 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '2' 1 sum=8 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '3' 1 sum=9 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '4' 0 sum=9 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '5' 1 sum=10 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'B' 1 sum=11 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '6' 0 sum=11 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '7' 1 sum=12 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'C' 0 sum=12 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '2' 1 sum=13 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '0' 0 sum=13 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '2' 1 sum=14 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '2' 1 sum=15 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'E' 0 sum=15 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'E' 0 sum=15 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'E' 0 sum=15 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'F' 0 sum=15 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'A' 0 sum=15 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'D' 1 sum=16 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '8' 0 sum=16 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '9' 0 sum=16 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '0' 0 sum=16 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'A' 0 sum=16 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'B' 1 sum=17 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'C' 0 sum=17 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'D' 1 sum=18 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'E' 0 sum=18 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'F' 0 sum=18 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '1' 0 sum=18 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '2' 1 sum=19 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '3' 1 sum=20 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '4' 0 sum=20 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* '5' 1 sum=21 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'B' 1 sum=22 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'B' 1 sum=23 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'B' 1 sum=24 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'B' 1 sum=25 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'A' 0 sum=25 *)
  simpl.
  unfold is_prime_hex_digit.
  simpl. (* 'A' 0 sum=25 *)
  simpl.
  reflexivity.
Qed.