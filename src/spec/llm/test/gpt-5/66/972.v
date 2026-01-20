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

Definition test_input : string :=
  String.append
    "tHisItabsBCDEFGHIJKLMNOPQRSTUVThis"
    (String (Ascii.ascii_of_nat 10)
       (String.append
          "is"
          (String (Ascii.ascii_of_nat 9)
             (String.append
                "tabsBCDEFGHIJKLMNOPQRS"
                (String (Ascii.ascii_of_nat 10)
                   (String.append
                      "is"
                      (String (Ascii.ascii_of_nat 9)
                         (String.append
                            "a"
                            (String (Ascii.ascii_of_nat 9)
                               (String.append
                                  "test"
                                  (String (Ascii.ascii_of_nat 9)
                                     "wiRNTERS"))))))))))).

Example digitSum_test_spec: digitSum_spec test_input 3644.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_test_Z: Z.of_nat (digitSum_fun test_input) = 3644%Z.
Proof.
  simpl.
  reflexivity.
Qed.