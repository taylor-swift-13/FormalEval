Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string : string :=
  String.append
    "Hello, WoG1234 This sitriThis is a long string that has many characters in itng has a "
    (String (Ascii.ascii_of_nat 10)
      (String.append
        " newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazby Thisthree"
        (String (Ascii.ascii_of_nat 10)
          (String.append
            "four"
            (String (Ascii.ascii_of_nat 10)
              "fiveracter dogQyadEborlod!"))))).

Example strlen_spec_case: strlen_spec test_string 235.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length test_string) = 235%Z.
Proof.
  simpl.
  reflexivity.
Qed.