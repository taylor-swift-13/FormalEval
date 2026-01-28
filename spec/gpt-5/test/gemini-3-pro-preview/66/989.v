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

Open Scope string_scope.

Definition input_str :=
  "tabsBCDEFTGHIJKLMNOPQRSTUVThis" ++ String (ascii_of_nat 10) "" ++
  "is" ++ String (ascii_of_nat 9) "" ++
  "tabiThissBCDEFGHIJKLMNOPQRS" ++ String (ascii_of_nat 10) "" ++
  "istabsWXYZ5nm5t4K5t5ms5t5m5t5n5t5r5t5s5t5n5n5M5t5s5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5nt5v5t5sn5t5M5t5n" ++ String (ascii_of_nat 9) "" ++
  "a" ++ String (ascii_of_nat 9) "" ++
  "twitwhtabsBCDEFGHIJKLMNOPQRSTUVThis" ++ String (ascii_of_nat 10) "" ++
  "is" ++ String (ascii_of_nat 9) "" ++
  "a" ++ String (ascii_of_nat 9) "" ++
  "test" ++ String (ascii_of_nat 9) "" ++
  "with" ++ String (ascii_of_nat 10) "" ++
  "newlineTh!s!s$0nly4t3st!ng-f5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5n5t5r5testt5s5ttestsIsaCrazyMiXofRUPPERandloWercaseLENTERSt5n5n5M5t5s5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5ns" ++ String (ascii_of_nat 9) "" ++
  "and" ++ String (ascii_of_nat 9) "" ++
  "tabsWXYAThisZest" ++ String (ascii_of_nat 9) "" ++
  "wiEth" ++ String (ascii_of_nat 10) "" ++
  "newlines" ++ String (ascii_of_nat 9) "" ++
  "a" ++ String (ascii_of_nat 9) "" ++
  "test" ++ String (ascii_of_nat 9) "" ++
  "tabsWDXYZ".

Example test_digitSum_long: digitSum_spec input_str 9467.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.