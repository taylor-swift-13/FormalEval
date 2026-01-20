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

Definition test_str : string :=
  String.append "This"
    (String (Ascii.ascii_of_nat 10)
       (String.append "is"
          (String (Ascii.ascii_of_nat 9)
             (String.append "a"
                (String (Ascii.ascii_of_nat 9)
                   (String.append "test"
                      (String (Ascii.ascii_of_nat 9)
                         (String.append "with"
                            (String (Ascii.ascii_of_nat 10)
                               (String.append "ntestestabsWXThiAThiswlines"
                                  (String (Ascii.ascii_of_nat 9)
                                     (String.append "and"
                                        (String (Ascii.ascii_of_nat 9)
                                           "tabsWDXYZtabs"))))))))))))).

Example digitSum_new_spec: digitSum_spec test_str 914.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_new_Z: Z.of_nat (digitSum_fun test_str) = 914%Z.
Proof.
  simpl.
  reflexivity.
Qed.