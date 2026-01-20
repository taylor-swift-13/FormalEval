Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in (97 <=? n) && (n <=? 122).

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in (65 <=? n) && (n <=? 90).

Definition flip_char (c : ascii) : ascii :=
  if is_lower c then ascii_of_nat (nat_of_ascii c - 32)
  else if is_upper c then ascii_of_nat (nat_of_ascii c + 32)
  else c.

Fixpoint flip_case_model (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (flip_char c) (flip_case_model s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_model s.

Example test_flip_case : flip_case_spec "opocπειρατέομαιএটিγνώμην একটtHe qτuIck πειρατέομαιএটিγνώμην একটtHe qτuIck bROwn fOX jUMPed ovePr the LAZY DOGি উদাহরQuiКлары্র bROwn fOX jUMPed ovePr the LAZY DOGি উদাহরQuiКлары্রo." "OPOCπειρατέομαιএটিγνώμην একটThE QτUiCK πειρατέομαιএটিγνώμην একটThE QτUiCK BroWN Fox JumpED OVEpR THE lazy dogি উদাহরqUIКлары্র BroWN Fox JumpED OVEpR THE lazy dogি উদাহরqUIКлары্রO.".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.