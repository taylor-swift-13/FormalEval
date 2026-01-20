Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Open Scope string_scope.

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
  "tabsBCDEFGHIJKLMNOPQRS" ++
  String (Ascii.ascii_of_nat 10)
    ("is" ++
      String (Ascii.ascii_of_nat 9)
        ("a" ++
          String (Ascii.ascii_of_nat 9)
            ("tesiWOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFLOWMYTEtabsBCDEFGHIJKLMNOPQRSTUVThisXTEFDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETTERS.sbsWDXYZ"))).

Example digitSum_new_spec: digitSum_spec test_input (digitSum_fun test_input).
Proof.
  unfold digitSum_spec.
  reflexivity.
Qed.

Example digitSum_new_Z: Z.of_nat (digitSum_fun test_input) = 11631%Z.
Proof.
  simpl.
  reflexivity.
Qed.