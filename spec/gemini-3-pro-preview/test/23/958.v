Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["thThT OaverThisBBrownLaazyLazye   t1t 1 The    iCVeLBrownLazazy"], output = 63 *)
Example test_strlen_complex : strlen_spec "thThT OaverThisBBrownLaazyLazye   t1t 1 The    iCVeLBrownLazazy" 63.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.