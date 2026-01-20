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

Example digitSum_case_spec: digitSum_spec "Th!s!s$0nly4t3st!ng-f5mm5g55gn5Tt5Th5t5yn5thy5ht5t$Bc&Def3@F5n" 456.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_case_Z: Z.of_nat (digitSum_fun "Th!s!s$0nly4t3st!ng-f5mm5g55gn5Tt5Th5t5yn5thy5ht5t$Bc&Def3@F5n") = 456%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.