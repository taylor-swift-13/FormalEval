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

(* Test case: input = ["TTacco"], output = false *)
Example test_palindrome_TTacco : is_palindrome_spec "TTacco" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "TTacco" *)
  simpl.
  
  (* The goal becomes: false = true <-> "TTacco" = "occaTT" *)
  split.
  - (* Left to Right: false = true -> "TTacco" = "occaTT" *)
    intros H.
    discriminate H.
  - (* Right to Left: "TTacco" = "occaTT" -> false = true *)
    intros H.
    discriminate H.
Qed.