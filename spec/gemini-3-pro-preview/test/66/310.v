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

Example test_digitSum_long : digitSum_spec "12345Th!s!s$0nly4t3st!sng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yn5thytHisIeLENTERSercaseLENTERSL5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5Th!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHope5t5sn5t5M5t5nv5t5sn5t5M5t5nUVWXYThis" 4408.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.