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

(* Test case: input = ["r"], output = true *)
Example test_palindrome_r : is_palindrome_spec "r" true.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "r" *)
  simpl.
  
  (* The goal becomes: true = true <-> "r" = "r" *)
  split.
  - (* Left to Right: true = true -> "r" = "r" *)
    intros H.
    reflexivity.
  - (* Right to Left: "r" = "r" -> true = true *)
    intros H.
    reflexivity.
Qed.