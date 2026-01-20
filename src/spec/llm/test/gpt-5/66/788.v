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

Example digitSum_long_spec: digitSum_spec "withWOWTHISISSUCHALONGSTTh!s!s$0nly4t3st!ng-f55S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5t1c&Def3@F5nRINGIWONDMERIFITWILLOVERFLOWMYCTEtabsBCDEFGHIJKLMNOPQRSTUVThisXTTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETTERS." (digitSum_fun "withWOWTHISISSUCHALONGSTTh!s!s$0nly4t3st!ng-f55S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5t1c&Def3@F5nRINGIWONDMERIFITWILLOVERFLOWMYCTEtabsBCDEFGHIJKLMNOPQRSTUVThisXTTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETTERS.").
Proof.
  unfold digitSum_spec.
  reflexivity.
Qed.

Example digitSum_long_Z: Z.of_nat (digitSum_fun "withWOWTHISISSUCHALONGSTTh!s!s$0nly4t3st!ng-f55S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5t1c&Def3@F5nRINGIWONDMERIFITWILLOVERFLOWMYCTEtabsBCDEFGHIJKLMNOPQRSTUVThisXTTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETTERS.") = 10406%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.