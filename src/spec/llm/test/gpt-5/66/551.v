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

Definition test_str : string :=
"THISISALONGSTRINGWITHMANYUPPERCASELETTisEThisTh!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWELL.t!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5maHELLOthereWHATareYOUdoingTODAY?IHopDeYOURdayISgoingWELL.dm5g55gn5t5Th05t5yn5thy5ht5t5S5t5b5t5m5t5ahCrazyMiXofUtPPERandloWercaseLENTERS5t5m5t5sn5ST5TS5THTHISISALONGSTRINGWITHMANYUPPERCASEL12345ABCDEFGHHELLOthereWHATarteYOUdoingTODAY?IHopeYOURdayISgoingWELL.JIJKLMNOPQRSTUVWXYZ67890ETTERSANDNOSPACESNDNOSPACESt5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5nRSANDNOSPACES".

Example digitSum_long_spec: digitSum_spec test_str 20184.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_long_Z: Z.of_nat (digitSum_fun test_str) = 20184%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.