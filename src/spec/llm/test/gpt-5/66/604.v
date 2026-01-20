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

Example digitSum_test_spec: digitSum_spec "ThisTh!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWELL.t!ng-1&2ABCDEFGHIJKLMNOPQRSTUVWXYZnewlines5shr5t5SS5t5v5t5sn5t5M5t5nZGxrhttabs" 4849.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_test_Z: Z.of_nat (digitSum_fun "ThisTh!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWELL.t!ng-1&2ABCDEFGHIJKLMNOPQRSTUVWXYZnewlines5shr5t5SS5t5v5t5sn5t5M5t5nZGxrhttabs") = 4849%Z.
Proof.
  simpl.
  reflexivity.
Qed.