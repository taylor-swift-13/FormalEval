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

Example test_digitSum_complex: digitSum_spec "tabsWDXYZ5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5n5t5r5testt5s5ttestsIsaCrazyMiXofRUPPERandloWercaseLENTERSt5n5n5M5t5s5t5m5t5sn5ST5TS5t5n5t5tn5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t55M5t5ns" 2710.
Proof.
  unfold digitSum_spec.
  reflexivity.
Qed.