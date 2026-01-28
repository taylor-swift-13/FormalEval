Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

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

Example test_digitSum_complex: digitSum_spec "aHELLOthereWHATareYOUdoingTODAABCDEFGHIJKLMTh!s!s$0nly4t3st!ng-1&2%3*4@5_.c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Tht5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5YZnewlinURdayISgoingWELL.dans" 3847.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.