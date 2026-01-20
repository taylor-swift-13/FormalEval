Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition test_str : string :=
  String.append "Testing te stingone"
    (String.append nl
      (String.append "twot"
        (String.append nl
          (String.append "thrThis is a long strinThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree"
            (String.append nl
              (String.append "four"
                (String.append nl
                  (String.append "fiveracter dogg that has many characters in itee"
                    (String.append nl
                      (String.append "four"
                        (String.append nl
                          "five 123"))))))))))).

Example strlen_spec_case: strlen_spec test_str 209.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Z: Z.of_nat (String.length test_str) = 209%Z.
Proof.
  simpl.
  reflexivity.
Qed.