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

(* Test case: input = ["Step on no pets"], output = false *)
Example test_palindrome_step_on_no_pets : is_palindrome_spec "Step on no pets" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "Step on no pets" = string_rev "Step on no pets" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    inversion H.
  - (* Right to Left: "Step on no pets" = string_rev ... -> false = true *)
    intros H.
    (* Compute the reverse string in the hypothesis *)
    simpl in H.
    (* The hypothesis H is now an equality between two different strings ("Step..." = "step...") *)
    (* Since the strings differ (case sensitivity), discriminate solves the contradiction *)
    discriminate H.
Qed.