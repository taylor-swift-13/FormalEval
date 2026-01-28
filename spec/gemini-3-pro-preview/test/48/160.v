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

(* Test case: input = ["ere"], output = true *)
Example test_palindrome_ere : is_palindrome_spec "ere" true.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "ere" *)
  simpl.
  
  (* The goal becomes: true = true <-> "ere" = "ere" *)
  split.
  - (* Left to Right: true = true -> "ere" = "ere" *)
    intros H.
    reflexivity.
  - (* Right to Left: "ere" = "ere" -> true = true *)
    intros H.
    reflexivity.
Qed.