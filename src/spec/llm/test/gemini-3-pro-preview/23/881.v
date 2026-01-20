Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

Example test_strlen_Jumpsw1Tntoghiss : strlen_spec "Jumpsw1Tntoghiss" 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.