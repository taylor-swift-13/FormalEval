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

Definition NL := String (ascii_of_nat 10) EmptyString.
Definition TAB := String (ascii_of_nat 9) EmptyString.

Example test_digitSum_long: digitSum_spec 
  ("witwhtabsBCDEFGHIJKLMNOPQRESTUVTstabsWXThiAThis" ++ NL ++ 
   "i" ++ NL ++ 
   "s" ++ TAB ++ "tteWercaseLENTERSa" ++ TAB ++ "test" ++ TAB ++ 
   "withWOWTHISISSUCIHALONGXSTRFFER.ITSJUSTSOMANYUPPERCASELETTERS." ++ NL ++ 
   "newlines" ++ TAB ++ "and" ++ TAB ++ "tabsBCDEFGHIJKLMNOPQRSTUVWXYZsZhis")%string 
  9187.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.