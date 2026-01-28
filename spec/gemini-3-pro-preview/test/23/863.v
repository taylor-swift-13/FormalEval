Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["ThT OverThisBBrownLaazyLazy   t1DomgmCV  i"], output = 42 *)
Example test_strlen_1 : strlen_spec "ThT OverThisBBrownLaazyLazy   t1DomgmCV  i" 42.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.