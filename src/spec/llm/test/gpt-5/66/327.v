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

Definition test_string : string :=
  String.append
    "tHisIsaCrazyMiXofUPPER1A$Bc&Decf3@FandloWeBrcaisThis"
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
                         (String.append
                            "with"
                            (String (Ascii.ascii_of_nat 10)
                               (String.append
                                  "newlines"
                                  (String (Ascii.ascii_of_nat 9)
                                     (String.append
                                        "and"
                                        (String (Ascii.ascii_of_nat 9)
                                           "tabsLENTERS"))))))))))))).

Example digitSum_new_spec: digitSum_spec test_string 1820.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_new_Z: Z.of_nat (digitSum_fun test_string) = 1820%Z.
Proof.
  simpl.
  reflexivity.
Qed.