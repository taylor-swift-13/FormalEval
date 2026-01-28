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

(* Test case: input = ["ca?t"], output = false *)
Example test_palindrome_cat : is_palindrome_spec "ca?t" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "ca?t" *)
  simpl.
  
  (* The goal becomes: false = true <-> "ca?t" = "t?ac" *)
  split.
  - (* Left to Right: false = true -> "ca?t" = "t?ac" *)
    intros H.
    discriminate H.
  - (* Right to Left: "ca?t" = "t?ac" -> false = true *)
    intros H.
    discriminate H.
Qed.