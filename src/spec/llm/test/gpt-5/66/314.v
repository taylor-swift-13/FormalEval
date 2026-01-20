Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.

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

Example digitSum_long_spec: digitSum_spec "12345Th!s!s$0nly4t3st!sng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yn5thytHisIeLENTERSercaseLENTERSL5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5Th!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHope5t5sn5t5M5t5nv5t5tHisIsaCrazyMiXofUPPEPRandloWercaseLENaTERSWXYThis" 5641.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_long_Z: Z.of_nat (digitSum_fun "12345Th!s!s$0nly4t3st!sng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yn5thytHisIeLENTERSercaseLENTERSL5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5Th!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHope5t5sn5t5M5t5nv5t5tHisIsaCrazyMiXofUPPEPRandloWercaseLENaTERSWXYThis") = 5641%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.