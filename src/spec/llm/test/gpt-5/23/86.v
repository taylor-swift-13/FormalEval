Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_multiline: strlen_spec
  ("one" ++ String (Ascii.ascii_of_nat 10) EmptyString ++
   "twota" ++ String (Ascii.ascii_of_nat 10) EmptyString ++
   "thrThis is a long string that has many characters ien itee" ++ String (Ascii.ascii_of_nat 10) EmptyString ++
   "four" ++ String (Ascii.ascii_of_nat 10) EmptyString ++
   "five") 78.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_multiline_Z:
  Z.of_nat (String.length
    ("one" ++ String (Ascii.ascii_of_nat 10) EmptyString ++
     "twota" ++ String (Ascii.ascii_of_nat 10) EmptyString ++
     "thrThis is a long string that has many characters ien itee" ++ String (Ascii.ascii_of_nat 10) EmptyString ++
     "four" ++ String (Ascii.ascii_of_nat 10) EmptyString ++
     "five")) = 78%Z.
Proof.
  simpl.
  reflexivity.
Qed.