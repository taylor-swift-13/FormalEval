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

Example digitSum_long_spec: digitSum_spec "tesiWOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFLOWMYTEtabsBCDEFGHIJKLMNOPQRSTUVThisXTEFDITOROREVENtHisItabbsBCDEFGHIJKLMNOPQRSTUVThis
is	tabsBCDEFGHIJKLMNOPQRS
is	a	test	with
newlines	and	AThistabsWXYAThisZa	test	tabsWDXYZsaCrazyMiXofRUPPERandloWercaseLENTERStabsTS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5nthALARGBUFFER.ITSJUSTSOMANYUPPERCASELETtTh!s!s$0nly4t3st!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5Th!s!s$0nly4t3sttabsBCDEFGHIJKLMNOPQRSTUVThisabsBCDEFGHIJKLMNOPQRSTUVWXYZDThisXTKTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETOTERS..sbsWDXYZiwth" 24604.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_long_Z: Z.of_nat (digitSum_fun "tesiWOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFLOWMYTEtabsBCDEFGHIJKLMNOPQRSTUVThisXTEFDITOROREVENtHisItabbsBCDEFGHIJKLMNOPQRSTUVThis
is	tabsBCDEFGHIJKLMNOPQRS
is	a	test	with
newlines	and	AThistabsWXYAThisZa	test	tabsWDXYZsaCrazyMiXofRUPPERandloWercaseLENTERStabsTS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5nthALARGBUFFER.ITSJUSTSOMANYUPPERCASELETtTh!s!s$0nly4t3st!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5Th!s!s$0nly4t3sttabsBCDEFGHIJKLMNOPQRSTUVThisabsBCDEFGHIJKLMNOPQRSTUVWXYZDThisXTKTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETOTERS..sbsWDXYZiwth") = 24604%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.