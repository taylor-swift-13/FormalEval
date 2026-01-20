Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string : string :=
  String (Ascii.ascii_of_nat 68)
    (String (Ascii.ascii_of_nat 235)
      (String (Ascii.ascii_of_nat 224)
        (String (Ascii.ascii_of_nat 232)
          (String (Ascii.ascii_of_nat 236)
            (String (Ascii.ascii_of_nat 242)
              (String (Ascii.ascii_of_nat 249)
                (String (Ascii.ascii_of_nat 104)
                  (String (Ascii.ascii_of_nat 121)
                    (String (Ascii.ascii_of_nat 78)
                      (String (Ascii.ascii_of_nat 74)
                        (String (Ascii.ascii_of_nat 99)
                          (String (Ascii.ascii_of_nat 74)
                            (String (Ascii.ascii_of_nat 245)
                              (String (Ascii.ascii_of_nat 228)
                                (String (Ascii.ascii_of_nat 235)
                                  (String (Ascii.ascii_of_nat 239)
                                    (String (Ascii.ascii_of_nat 255)
                                      (String (Ascii.ascii_of_nat 231)
                                        (String (Ascii.ascii_of_nat 103) EmptyString))))))))))))))))))).

Example strlen_spec_accented: strlen_spec test_string 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_accented_Z: Z.of_nat (String.length test_string) = 20%Z.
Proof.
  simpl.
  reflexivity.
Qed.