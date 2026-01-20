Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_multiline: strlen_spec
  (String (ascii_of_nat 32)
    (String (ascii_of_nat 32)
      (String (ascii_of_nat 32)
        (String (ascii_of_nat 10)
          (String (ascii_of_nat 10)
            (String (ascii_of_nat 66)
              (String (ascii_of_nat 114)
                (String (ascii_of_nat 111)
                  (String (ascii_of_nat 119)
                    (String (ascii_of_nat 110) EmptyString))))))))))
  10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_multiline_Z:
  Z.of_nat (String.length
    (String (ascii_of_nat 32)
      (String (ascii_of_nat 32)
        (String (ascii_of_nat 32)
          (String (ascii_of_nat 10)
            (String (ascii_of_nat 10)
              (String (ascii_of_nat 66)
                (String (ascii_of_nat 114)
                  (String (ascii_of_nat 111)
                    (String (ascii_of_nat 119)
                      (String (ascii_of_nat 110) EmptyString)))))))))))
  = 10%Z.
Proof.
  simpl.
  reflexivity.
Qed.