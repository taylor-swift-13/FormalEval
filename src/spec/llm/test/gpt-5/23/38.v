Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_multiline: strlen_spec "thrieeThe quick brown fox jumps overq the lazy dog
four
five" 60.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_multiline_Z: Z.of_nat (String.length "thrieeThe quick brown fox jumps overq the lazy dog
four
five") = 60%Z.
Proof.
  simpl.
  reflexivity.
Qed.