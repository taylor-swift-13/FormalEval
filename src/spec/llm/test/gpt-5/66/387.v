Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Fixpoint digitSum_fun (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String ch rest =>
      let code := nat_of_ascii ch in
      let is_upper := andb (Nat.leb 65 code) (Nat.leb code 90) in
      (if is_upper then code else 0) + digitSum_fun rest
  end.

Definition digitSum_spec (s : string) (sum : nat) : Prop :=
  sum = digitSum_fun s.

Example digitSum_test_spec: digitSum_spec "Th!s!s$0nly4t3st!ng-1&2%3*4@5seLENTERS5t5m5t5sn5ST5TS5t5n5t5n5t12345AB05Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5n" 1398.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_test_Z: Z.of_nat (digitSum_fun "Th!s!s$0nly4t3st!ng-1&2%3*4@5seLENTERS5t5m5t5sn5ST5TS5t5n5t5n5t12345AB05Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5n") = 1398%Z.
Proof.
  simpl.
  reflexivity.
Qed.