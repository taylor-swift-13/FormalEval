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

(* Test case: input = ["12zZ21"], output = false *)
Example test_palindrome_case_sensitive : is_palindrome_spec "12zZ21" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "12zZ21" to "12Zz21" *)
  simpl.
  
  (* The goal becomes: false = true <-> "12zZ21" = "12Zz21" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* Contradiction: false is not true *)
    discriminate.
  - (* Right to Left: "12zZ21" = "12Zz21" -> ... *)
    intros H.
    (* Contradiction: The strings differ at the character 'z' vs 'Z' *)
    discriminate.
Qed.