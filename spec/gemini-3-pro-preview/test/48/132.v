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

(* Test case: input = ["Step"], output = false *)
Example test_palindrome_step : is_palindrome_spec "Step" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Step" to "petS" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Step" = "petS" *)
  split.
  - (* Left to Right: false = true -> "Step" = "petS" *)
    intros H.
    discriminate H.
  - (* Right to Left: "Step" = "petS" -> false = true *)
    intros H.
    discriminate H.
Qed.