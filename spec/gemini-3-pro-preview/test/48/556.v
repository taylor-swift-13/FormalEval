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

(* Test case: input = ["e.a"], output = false *)
Example test_palindrome_ea : is_palindrome_spec "e.a" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "e.a" *)
  simpl.
  
  (* The goal becomes: false = true <-> "e.a" = "a.e" *)
  split.
  - (* Left to Right: false = true -> "e.a" = "a.e" *)
    intros H.
    discriminate H.
  - (* Right to Left: "e.a" = "a.e" -> false = true *)
    intros H.
    discriminate H.
Qed.