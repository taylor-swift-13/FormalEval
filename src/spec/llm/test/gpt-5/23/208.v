Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_str : string :=
  String " "%char
    (String " "%char
      (String " "%char
        (String " "%char
          (String "4"%char
            (String (Ascii.ascii_of_nat 10)
              (String (Ascii.ascii_of_nat 10)
                (String " "%char
                  (String " "%char
                    (String "1"%char
                      (String "s"%char
                        (String " "%char
                          (String " "%char EmptyString)))))))))))).

Example strlen_spec_new: strlen_spec test_str 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length test_str) = 13%Z.
Proof.
  simpl.
  reflexivity.
Qed.