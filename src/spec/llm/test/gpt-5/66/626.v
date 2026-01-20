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

Example digitSum_text_spec: digitSum_spec ("AThis
is	a	test	with
newlines	and	tabsBCDEFGHIJKLMNOPQRSTUVWXYZ")%string 2099.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_text_Z: Z.of_nat (digitSum_fun ("AThis
is	a	test	with
newlines	and	tabsBCDEFGHIJKLMNOPQRSTUVWXYZ")%string) = 2099%Z.
Proof.
  simpl.
  reflexivity.
Qed.