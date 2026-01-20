Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Fixpoint str_append (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String ch rest => String ch (str_append rest s2)
  end.

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

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.
Definition tab : string := String (Ascii.ascii_of_nat 9) EmptyString.

Definition test_input : string :=
  str_append "This"
    (str_append nl
      (str_append "is"
        (str_append tab
          (str_append "a"
            (str_append tab
              (str_append "test"
                (str_append tab
                  (str_append "with"
                    (str_append nl
                      (str_append "newlines"
                        (str_append tab "asns"))))))))))).

Example digitSum_test_spec: digitSum_spec test_input 84.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_test_Z: Z.of_nat (digitSum_fun test_input) = 84%Z.
Proof.
  simpl.
  reflexivity.
Qed.