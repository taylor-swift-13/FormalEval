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

Definition s_test : string :=
"aaaaMaABCDEFGHIJKABCDEThis
is	a	test	with
newlines	ansFGHIJKLMNOPQRSTThisTh!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWELL.t!ng-1&2ABCDEFGHIJKLMNOPQRSTUVWXYZnewlines5shr5t5SS5t5v5t5sn5t5M5Ut5nUVWXYZnewlindLMNOPQRSTUVWXYZbbbbbbccccccdddeeefffggggHHHHHIIIIJJJJKKKKLLLLMMMMNNNaaaETTHERSANDNOSPACESNDNOSPACESTTTUUVVVVWWWXXXYYYZZJZ".

Example digitSum_test_spec: digitSum_spec s_test 15068.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_test_Z: Z.of_nat (digitSum_fun s_test) = 15068%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.