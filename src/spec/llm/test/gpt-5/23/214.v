Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition accented_string : string :=
  String (Ascii.ascii_of_nat 224)
    (String (Ascii.ascii_of_nat 232)
      (String (Ascii.ascii_of_nat 236)
        (String (Ascii.ascii_of_nat 242)
          (String (Ascii.ascii_of_nat 249)
            (String (Ascii.ascii_of_nat 225)
              (String (Ascii.ascii_of_nat 233)
                (String (Ascii.ascii_of_nat 237)
                  (String (Ascii.ascii_of_nat 243)
                    (String (Ascii.ascii_of_nat 250)
                      (String (Ascii.ascii_of_nat 253)
                        (String (Ascii.ascii_of_nat 226)
                          (String (Ascii.ascii_of_nat 234)
                            (String (Ascii.ascii_of_nat 238)
                              (String (Ascii.ascii_of_nat 232)
                                (String (Ascii.ascii_of_nat 244)
                                  (String (Ascii.ascii_of_nat 251)
                                    (String (Ascii.ascii_of_nat 227)
                                      (String (Ascii.ascii_of_nat 241)
                                        (String (Ascii.ascii_of_nat 245)
                                          (String (Ascii.ascii_of_nat 228)
                                            (String (Ascii.ascii_of_nat 235)
                                              (String (Ascii.ascii_of_nat 239)
                                                (String (Ascii.ascii_of_nat 246)
                                                  (String (Ascii.ascii_of_nat 252)
                                                    (String (Ascii.ascii_of_nat 255)
                                                      (String (Ascii.ascii_of_nat 231)
                                                        EmptyString)))))))))))))))))))))))))).

Example strlen_spec_accented: strlen_spec accented_string 27.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_accented_Z: Z.of_nat (String.length accented_string) = 27%Z.
Proof.
  simpl.
  reflexivity.
Qed.