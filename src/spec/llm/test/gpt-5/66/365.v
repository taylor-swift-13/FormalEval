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

Definition test_string : string :=
"THISISALONGSTRINGWITHMANYUPPERCASELETTisERSANDNOSPWOWLONGSTRINGIWONDERIFITWILLYOVERFLOWMYTEXTEDITOROREVENALARGBUFFER.ETTERS.ACESWOWTHISCISSUCHALONGSTRINGIWONDEABCDMNOPMQRSTUVWXYZnewlinesLOWMYTEXTEDITOROREVENALARGBUFFER.ETTERS.".

Example digitSum_long_spec: digitSum_spec test_string 16373.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_long_Z: Z.of_nat (digitSum_fun test_string) = 16373%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.