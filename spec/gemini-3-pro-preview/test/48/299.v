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

(* Test case: input = ["1Ws"], output = false *)
Example test_palindrome_1Ws : is_palindrome_spec "1Ws" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "1Ws" *)
  simpl.
  
  (* The goal becomes: false = true <-> "1Ws" = "sW1" *)
  split.
  - (* Left to Right: false = true -> "1Ws" = "sW1" *)
    intros H.
    discriminate H.
  - (* Right to Left: "1Ws" = "sW1" -> false = true *)
    intros H.
    discriminate H.
Qed.