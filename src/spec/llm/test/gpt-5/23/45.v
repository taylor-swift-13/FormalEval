Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string : string :=
  String.append "one"
    (String (Ascii.ascii_of_nat 10)
      (String.append "twota"
        (String (Ascii.ascii_of_nat 10)
          (String.append "thrThis is a long string that has many characters in itee"
            (String (Ascii.ascii_of_nat 10)
              (String.append "four"
                (String (Ascii.ascii_of_nat 10) "five"))))))).

Example strlen_spec_test: strlen_spec test_string 77.
Proof.
  unfold strlen_spec.
  unfold test_string.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Z: Z.of_nat (String.length test_string) = 77%Z.
Proof.
  unfold test_string.
  simpl.
  reflexivity.
Qed.