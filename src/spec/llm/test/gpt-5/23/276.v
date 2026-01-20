Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_str : string :=
  String (Ascii.ascii_of_nat 32)
    (String (Ascii.ascii_of_nat 84)
      (String (Ascii.ascii_of_nat 104)
        (String (Ascii.ascii_of_nat 33)
          (String (Ascii.ascii_of_nat 115)
            (String (Ascii.ascii_of_nat 32)
              (String (Ascii.ascii_of_nat 32)
                (String (Ascii.ascii_of_nat 10)
                  (String (Ascii.ascii_of_nat 10)
                    (String (Ascii.ascii_of_nat 32)
                      (String (Ascii.ascii_of_nat 49)
                        (String (Ascii.ascii_of_nat 115)
                          (String (Ascii.ascii_of_nat 32)
                            (String (Ascii.ascii_of_nat 32)
                              EmptyString))))))))))))).

Example strlen_spec_new: strlen_spec test_str 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length test_str) = 14%Z.
Proof.
  simpl.
  reflexivity.
Qed.