Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Local Open Scope string_scope.

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

Definition newline : string := String (Ascii.ascii_of_nat 10) EmptyString.
Definition tab : string := String (Ascii.ascii_of_nat 9) EmptyString.

Definition input_string : string :=
  "This" ++
  newline ++
  "THISISALONGSTRINGWITHMANYUPPERCASEL12345ABCDEFGHJIJKLMNOPQRSTUVWXYZ67890ETTERSANDNOSPACESis" ++
  tab ++
  "a" ++
  tab ++
  "test" ++
  tab ++
  "with" ++
  newline ++
  "newleidnes" ++
  tab ++
  "dand" ++
  tab ++
  "tabss".

Example digitSum_case_spec: digitSum_spec input_string 6148.
Proof.
  unfold digitSum_spec.
  unfold input_string, newline, tab.
  simpl.
  reflexivity.
Qed.

Example digitSum_case_Z: Z.of_nat (digitSum_fun input_string) = 6148%Z.
Proof.
  unfold input_string, newline, tab.
  simpl.
  reflexivity.
Qed.