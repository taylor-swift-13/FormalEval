Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition s_CQuicJumpsk_cr : string :=
  String (Ascii.ascii_of_nat 67)
    (String (Ascii.ascii_of_nat 81)
      (String (Ascii.ascii_of_nat 117)
        (String (Ascii.ascii_of_nat 105)
          (String (Ascii.ascii_of_nat 99)
            (String (Ascii.ascii_of_nat 74)
              (String (Ascii.ascii_of_nat 117)
                (String (Ascii.ascii_of_nat 109)
                  (String (Ascii.ascii_of_nat 112)
                    (String (Ascii.ascii_of_nat 115)
                      (String (Ascii.ascii_of_nat 107)
                        (String (Ascii.ascii_of_nat 13) EmptyString))))))))))).

Example strlen_spec_CQuicJumpsk_cr: strlen_spec s_CQuicJumpsk_cr 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_CQuicJumpsk_cr_Z: Z.of_nat (String.length s_CQuicJumpsk_cr) = 12%Z.
Proof.
  simpl.
  reflexivity.
Qed.