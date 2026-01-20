Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_of_foive: strlen_spec
  (String (Ascii.ascii_of_nat 111)
    (String (Ascii.ascii_of_nat 102)
      (String (Ascii.ascii_of_nat 10)
        (String (Ascii.ascii_of_nat 102)
          (String (Ascii.ascii_of_nat 111)
            (String (Ascii.ascii_of_nat 105)
              (String (Ascii.ascii_of_nat 118)
                (String (Ascii.ascii_of_nat 101) EmptyString)))))))) 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_of_foive_Z:
  Z.of_nat (String.length
    (String (Ascii.ascii_of_nat 111)
      (String (Ascii.ascii_of_nat 102)
        (String (Ascii.ascii_of_nat 10)
          (String (Ascii.ascii_of_nat 102)
            (String (Ascii.ascii_of_nat 111)
              (String (Ascii.ascii_of_nat 105)
                (String (Ascii.ascii_of_nat 118)
                  (String (Ascii.ascii_of_nat 101) EmptyString))))))))) = 8%Z.
Proof.
  simpl.
  reflexivity.
Qed.