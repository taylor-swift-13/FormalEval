Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Open Scope string_scope.

(* Function definition as provided in the specification *)
Fixpoint string_rev (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (string_rev s') ++ (String c EmptyString)
  end.

(* Specification definition as provided *)
Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  result = true <-> text = string_rev text.

(* Test case: input = ["Step osawn no pets"], output = false *)
Example test_palindrome_step_osawn_no_pets : is_palindrome_spec "Step osawn no pets" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev *)
  simpl.
  
  (* The goal becomes: false = true <-> "Step osawn no pets" = "step on nwaso petS" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    inversion H.
  - (* Right to Left: "Step osawn no pets" = "step on nwaso petS" -> false = true *)
    intros H.
    inversion H.
Qed.