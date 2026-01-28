Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90).

Fixpoint digitSum_calc (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
      if is_upper c then (nat_of_ascii c) + (digitSum_calc s')
      else digitSum_calc s'
  end.

Definition digitSum_spec (s : string) (result : nat) : Prop :=
  result = digitSum_calc s.

Example test_digitSum_long : digitSum_spec "1X6YZ6789ThisTh!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWELL.t!ng-1&2ABCDEFGHIJKLMNOPQRSTUVWXYZnewlines5shr5t5SS5t5v5t5sn5t5M5t5n0" 4955.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.