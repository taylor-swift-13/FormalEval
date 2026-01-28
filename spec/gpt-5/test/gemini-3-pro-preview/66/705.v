Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
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

Definition test_input : string :=
  "AThis" ++ String (ascii_of_nat 10) "" ++
  "is" ++ String (ascii_of_nat 9) "" ++ "a" ++ String (ascii_of_nat 9) "" ++ "test" ++ String (ascii_of_nat 9) "" ++ "withWOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFLOWMYTEtabsBCDEFGHIJKLMNOPQittabsBCDEFGHIOJKLMNOPQRSshROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETTERS." ++ String (ascii_of_nat 10) "" ++
  "newlines" ++ String (ascii_of_nat 9) "" ++ "and" ++ String (ascii_of_nat 9) "" ++ "tabsBCDEFGHIJKLMNOPQRSTUVWXYZ".

Example test_digitSum_long: digitSum_spec test_input 12268.
Proof.
  unfold digitSum_spec.
  unfold test_input.
  vm_compute.
  reflexivity.
Qed.