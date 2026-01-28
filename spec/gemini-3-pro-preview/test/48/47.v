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

(* Test case: input = ["babbabcca"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "babbabcca" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "babbabcca" *)
  simpl.
  
  (* The goal becomes: false = true <-> "babbabcca" = "accbabbab" *)
  split.
  - (* Left to Right: false = true -> "babbabcca" = "accbabbab" *)
    intros H.
    (* Contradiction: false is not equal to true *)
    discriminate.
  - (* Right to Left: "babbabcca" = "accbabbab" -> false = true *)
    intros H.
    (* Contradiction: The strings are distinct *)
    discriminate.
Qed.