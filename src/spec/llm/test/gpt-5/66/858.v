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
  "Th!s!s$0nly4t3st!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5Th!s!s$0nly4t3sttabsBCDEFGHIJKLMNOPQRSTUVThis is tabsBCDEFGHIJKLMNOPQRS is a test with newlines and wiTh!s!s$0nly4t3st!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5n5t5r5testt5s5t5n5n5M5t5s5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5nthtabsWXYAThisZa test tabsWDXYZ!ng-f5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5testt5s5tt5v5t5sn5t5M5t1A$Bc&Def3@F5nt5yn5thy5ht5t5S5t5b5t5m5t5nm5tK5t5ms55t5m5t5n5t5r5testt55s5t5n5n5M5t5s5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5n".

Example digitSum_case_spec: digitSum_spec test_string (digitSum_fun test_string).
Proof.
  unfold digitSum_spec.
  reflexivity.
Qed.

Example digitSum_case_Z: Z.of_nat (digitSum_fun test_string) = 7012%Z.
Proof.
  simpl.
  reflexivity.
Qed.