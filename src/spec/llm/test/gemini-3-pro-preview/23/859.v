Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "     str1ng 1t  The    This is a samThT    1sampLazylet 1 The  MNhqThe CuQuicJumpsk Brown Fo    

   xstr1str1ngng Jumps OverThis is a sample string to test thCVt the function" 175.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.