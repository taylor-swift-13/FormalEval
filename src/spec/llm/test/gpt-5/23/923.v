Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Jumpsw1TntoghiTTBrisss: strlen_spec "Jumpsw1TntoghiTTBrisss"%string 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Jumpsw1TntoghiTTBrisss_Z: Z.of_nat (String.length "Jumpsw1TntoghiTTBrisss"%string) = 22%Z.
Proof.
  simpl.
  reflexivity.
Qed.