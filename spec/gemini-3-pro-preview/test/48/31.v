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

(* Test case: input = ["abbcc"], output = false *)
Example test_palindrome_abbcc : is_palindrome_spec "abbcc" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "abbcc" *)
  simpl.
  
  (* The goal becomes: false = true <-> "abbcc" = "ccbba" *)
  split.
  - (* Left to Right: false = true -> "abbcc" = "ccbba" *)
    intros H.
    discriminate H.
  - (* Right to Left: "abbcc" = "ccbba" -> false = true *)
    intros H.
    discriminate H.
Qed.