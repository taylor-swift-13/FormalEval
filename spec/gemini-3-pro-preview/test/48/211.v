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

(* Test case: input = ["sawa"], output = false *)
Example test_palindrome_sawa : is_palindrome_spec "sawa" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "sawa" *)
  simpl.
  
  (* The goal becomes: false = true <-> "sawa" = "awas" *)
  split.
  - (* Left to Right: false = true -> "sawa" = "awas" *)
    intros H.
    discriminate H.
  - (* Right to Left: "sawa" = "awas" -> false = true *)
    intros H.
    discriminate H.
Qed.