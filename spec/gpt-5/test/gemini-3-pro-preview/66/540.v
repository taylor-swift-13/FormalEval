Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

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

Example test_digitSum_large: digitSum_spec "Th!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHopeYO5URdayISgoingWELL.t!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yMn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5tHisRIsaCrazyMiXofUPPERandloWercaseLENTERS5t5m5t5sn5ST5TSt5SS5t5v5t5sn5t5M5t5n" 4877.
Proof.
  reflexivity.
Qed.