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

(* Test case: input = ["aaaabca"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "aaaabca" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "aaaabca" *)
  simpl.
  
  (* The goal becomes: false = true <-> "aaaabca" = "acbaaaa" *)
  split.
  - (* Left to Right: false = true -> "aaaabca" = "acbaaaa" *)
    intros H.
    inversion H.
  - (* Right to Left: "aaaabca" = "acbaaaa" -> false = true *)
    intros H.
    inversion H.
Qed.