Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90).

Fixpoint digitSum_calc (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
      if is_upper c then (nat_of_ascii c) + (digitSum_calc s')
      else digitSum_calc s'
  end.

Definition digitSum_spec (s : string) (result : nat) : Prop :=
  result = digitSum_calc s.

Example test_digitSum_complex : digitSum_spec "abcd1123A12:;<=>?@[\]^_`3{|}~ABC123def456GHI3BCD" 680.
Proof.
  unfold digitSum_spec.
  compute.
  reflexivity.
Qed.