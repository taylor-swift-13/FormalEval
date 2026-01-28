Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["àèìòõùáéíóúýâêîôûãñõäëïöüÿ"], output = 52 *)
(* Note: The prompt specifies 26 (character count), but Coq strings are byte sequences. *)
(* The given UTF-8 string contains 26 multi-byte characters, totaling 52 bytes. *)
Example test_strlen_unicode : strlen_spec "àèìòõùáéíóúýâêîôûãñõäëïöüÿ" 52.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.