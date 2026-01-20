Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec (String.append "MNhqThe CQuick Brown hFox Jumps OcveMNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCVr The BrownLazy DoMNhqmCdCQuicJumpsk" (String (Ascii.ascii_of_nat 13) "gmCV")) 154.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length (String.append "MNhqThe CQuick Brown hFox Jumps OcveMNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCVr The BrownLazy DoMNhqmCdCQuicJumpsk" (String (Ascii.ascii_of_nat 13) "gmCV"))) = 154%Z.
Proof.
  simpl.
  reflexivity.
Qed.