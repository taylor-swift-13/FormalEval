Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Local Open Scope string_scope.

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

Definition lf : string := String (Ascii.ascii_of_nat 10) EmptyString.
Definition tab : string := String (Ascii.ascii_of_nat 9) EmptyString.

Definition digitSum_test_input : string :=
  "witwhtabsBCDEFGHIJKLMNOPQRSTUVThis"
  ++ lf ++ "is" ++ tab ++ "a" ++ tab ++ "test" ++ tab ++ "with"
  ++ lf ++ "newlintabstesteTh!s!s$0nly4t3st!ng-f5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5n5t5r5testt5s5ttTHISISALONGSTRINEGWITHMANYUPPERCASELETTERSANDNOSPACESestsIsaCrazyMiXofRUPPERandloWercaseLENTERSt5n5Mn5M5t5s5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5ns"
  ++ tab ++ "and" ++ tab ++ "tabsWXYAThisZ".

Example digitSum_test_spec: digitSum_spec digitSum_test_input 8760.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_test_Z: Z.of_nat (digitSum_fun digitSum_test_input) = 8760%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.