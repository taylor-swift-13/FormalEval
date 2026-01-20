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

Definition input_string :=
"tHisItabsBCDEFGHIJKLMNOPQRSTUVThis
is	tabsBCDEFGHIJKLMNOPQRS
is	a	test	with
newlines	and	tabsWXYAThisZa	test	tabsWDXYZsaCraMiXofRUPPERandloWercaseLENTERS"%string.

Example digitSum_case_spec: digitSum_spec input_string (digitSum_fun input_string).
Proof.
  unfold digitSum_spec.
  reflexivity.
Qed.

Example digitSum_case_Z: Z.of_nat (digitSum_fun input_string) = 5429%Z.
Proof.
  compute.
  reflexivity.
Qed.