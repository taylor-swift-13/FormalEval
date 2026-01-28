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

(* Test case: input = ["I"], output = true *)
Example test_palindrome_I : is_palindrome_spec "I" true.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "I" *)
  simpl.
  
  (* The goal becomes: true = true <-> "I" = "I" *)
  split.
  - (* Left to Right: true = true -> "I" = "I" *)
    intros H.
    reflexivity.
  - (* Right to Left: "I" = "I" -> true = true *)
    intros H.
    reflexivity.
Qed.