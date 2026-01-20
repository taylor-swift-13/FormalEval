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

Definition nl := String (Ascii.ascii_of_nat 10) EmptyString.
Definition tb := String (Ascii.ascii_of_nat 9) EmptyString.

Definition inputStr :=
  String.append
    (String.append "witwhtabsBCDEFGHIJKLMNOPQRESTUVThis" nl)
    (String.append
        "is"
        (String.append tb
          (String.append "a"
             (String.append tb
                (String.append "tabstest"
                   (String.append tb
                      (String.append "with"
                         (String.append nl
                            (String.append "newlines"
                              (String.append tb
                                (String.append "and"
                                  (String.append tb "tabsWXYAThisZ")))))))))))).

Example digitSum_case_spec: digitSum_spec inputStr 2252.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_case_Z: Z.of_nat (digitSum_fun inputStr) = 2252%Z.
Proof.
  simpl.
  reflexivity.
Qed.