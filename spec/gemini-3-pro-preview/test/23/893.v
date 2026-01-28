Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["UcBwDnomgmCVownisLazyLazy"], output = 25 *)
Example test_strlen_UcBwDnomgmCVownisLazyLazy : strlen_spec "UcBwDnomgmCVownisLazyLazy" 25.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.