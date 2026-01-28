Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["ThT OverThisBBrownLaazyLazy   t1t 1 The    i"], output = 44 *)
Example test_strlen_complex : strlen_spec "ThT OverThisBBrownLaazyLazy   t1t 1 The    i" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.