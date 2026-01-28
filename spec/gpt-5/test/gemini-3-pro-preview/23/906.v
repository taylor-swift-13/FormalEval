Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "     str1ng 1t  The    This is a samThT    1sampLazylet i1 The  MNhqThe CuQuicJumpBsk Brown Fo    

   xstr1str1ngng Jumps OverThis is a sample string to test thCVt the function" 177.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.