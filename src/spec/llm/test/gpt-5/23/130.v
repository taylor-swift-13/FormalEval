Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string : string :=
  String (Ascii.ascii_of_nat 32)
    (String (Ascii.ascii_of_nat 32)
      (String (Ascii.ascii_of_nat 32)
        (String (Ascii.ascii_of_nat 32)
          (String (Ascii.ascii_of_nat 10)
            (String (Ascii.ascii_of_nat 32)
              (String (Ascii.ascii_of_nat 32)
                (String (Ascii.ascii_of_nat 115)
                  (String (Ascii.ascii_of_nat 116)
                    (String (Ascii.ascii_of_nat 114)
                      (String (Ascii.ascii_of_nat 105)
                        (String (Ascii.ascii_of_nat 110)
                          (String (Ascii.ascii_of_nat 103) EmptyString)))))))))))).

Example strlen_spec_spaces_newline_string: strlen_spec test_string 13.
Proof.
  unfold strlen_spec.
  unfold test_string.
  simpl.
  reflexivity.
Qed.

Example strlen_test_spaces_newline_string_Z: Z.of_nat (String.length test_string) = 13%Z.
Proof.
  unfold test_string.
  simpl.
  reflexivity.
Qed.