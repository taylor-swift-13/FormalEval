Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition s_test : string :=
  String (Ascii.ascii_of_nat 32)
    (String (Ascii.ascii_of_nat 32)
      (String (Ascii.ascii_of_nat 32)
        (String (Ascii.ascii_of_nat 13)
          (String (Ascii.ascii_of_nat 10)
            (String (Ascii.ascii_of_nat 32)
              (String (Ascii.ascii_of_nat 32)
                (String (Ascii.ascii_of_nat 32)
                  (String (Ascii.ascii_of_nat 32) EmptyString)))))))).

Example strlen_spec_spaces_crlf_spaces: strlen_spec s_test 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_spaces_crlf_spaces_Z: Z.of_nat (String.length s_test) = 9%Z.
Proof.
  simpl.
  reflexivity.
Qed.