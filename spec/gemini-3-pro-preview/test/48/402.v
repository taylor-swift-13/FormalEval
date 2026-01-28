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

(* Test case: input = ["122zZ2"], output = false *)
Example test_palindrome_122zZ2 : is_palindrome_spec "122zZ2" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "122zZ2" *)
  simpl.
  
  (* The goal becomes: false = true <-> "122zZ2" = "2Zz221" *)
  split.
  - (* Left to Right: false = true -> "122zZ2" = "2Zz221" *)
    intros H.
    discriminate H.
  - (* Right to Left: "122zZ2" = "2Zz221" -> false = true *)
    intros H.
    discriminate H.
Qed.