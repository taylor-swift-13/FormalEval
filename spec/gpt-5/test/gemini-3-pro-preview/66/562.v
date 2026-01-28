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

Example test_digitSum_1: digitSum_spec "T12345ABCDEFGHJIJKLMTHTHISISALONGSTRINGWITHMANYUPPERCASEL12345ABCDEFGHJIJKLMNOPQRSTUVWXYZ67890ETTHERSANDNOSPACESNDNOSPACESNOPQRSTUVWXYWOWTHISISSUCHALONGSTRINGIWONABCDEFGHIJKLMNOPQRSTUVWXYZnewlinesandOSPACES" 13851.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.