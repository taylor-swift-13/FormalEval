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

Definition test_string : string :=
"withWOWTHISISSUCHALONGSETRINGIWONDMERIFITWILLOVERFLOWMYTEtabAThis
is	a	test	withWOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFLOWMYTEtabsBCDEFGHIJKLMNOPQittabsBCDEFGHIOJKLMNOPQRSshROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETTtabsbBCDEFsERS.
newlines	and	tabsBCDEFGHIJKLMNOPQRSTUVWXYZDThisXTTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETOTERS.".

Example digitSum_test_spec: digitSum_spec test_string (digitSum_fun test_string).
Proof.
  unfold digitSum_spec.
  reflexivity.
Qed.

Example digitSum_test_Z: Z.of_nat (digitSum_fun test_string) = 21187%Z.
Proof.
  reflexivity.
Qed.