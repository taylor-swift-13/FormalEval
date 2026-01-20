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

Example digitSum_complex_spec: digitSum_spec "tHisIsaCrazyMiXofUPPLER1A$Bc&Decf3@FandloWeBrcaisThis\nis\ta\ttest\twith\nnewlines\tand\ttabsLENTERS" 1896.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_complex_Z: Z.of_nat (digitSum_fun "tHisIsaCrazyMiXofUPPLER1A$Bc&Decf3@FandloWeBrcaisThis\nis\ta\ttest\twith\nnewlines\tand\ttabsLENTERS") = 1896%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.