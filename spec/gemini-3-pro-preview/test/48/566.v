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

(* Test case: input = ["12zZaTaccliveo"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "12zZaTaccliveo" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev to its concrete value *)
  simpl.
  
  (* The goal becomes: false = true <-> "12zZaTaccliveo" = "oevilccaTaZz21" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: "12zZaTaccliveo" = "oevilccaTaZz21" -> ... *)
    intros H.
    discriminate.
Qed.