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

(* Test case: input = ["o"], output = true *)
Example test_palindrome_single : is_palindrome_spec "o" true.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "o" *)
  simpl.
  
  (* The goal becomes: true = true <-> "o" = "o" *)
  split.
  - (* Left to Right: true = true -> "o" = "o" *)
    intros H.
    reflexivity.
  - (* Right to Left: "o" = "o" -> true = true *)
    intros H.
    reflexivity.
Qed.