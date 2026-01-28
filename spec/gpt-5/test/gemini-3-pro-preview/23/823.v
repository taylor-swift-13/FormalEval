Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "     str1ng 1t  The    This is a samThT    1sampLazylet 1 The    ipleOvering to test the function" 97.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.