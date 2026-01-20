Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Dàèìòù4áéíóúýp1ssâêîôcJH1thûãñõäëïöüÿçgog"], output = 67 *)
(* Note: The input string contains multi-byte UTF-8 characters. 
   Coq's String.length counts bytes, resulting in 67 instead of 41 characters. *)
Example test_strlen_complex : strlen_spec "Dàèìòù4áéíóúýp1ssâêîôcJH1thûãñõäëïöüÿçgog" 67.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.