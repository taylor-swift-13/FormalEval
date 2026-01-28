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

(* Test case: input = ["or"], output = false *)
Example test_palindrome_or : is_palindrome_spec "or" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "or" *)
  simpl.
  
  (* The goal becomes: false = true <-> "or" = "ro" *)
  split.
  - (* Left to Right: false = true -> "or" = "ro" *)
    intros H.
    discriminate.
  - (* Right to Left: "or" = "ro" -> false = true *)
    intros H.
    discriminate.
Qed.