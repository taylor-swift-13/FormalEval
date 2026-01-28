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

(* Test case: input = ["ba"], output = false *)
Example test_palindrome_ba : is_palindrome_spec "ba" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "ba" *)
  simpl.
  
  (* The goal becomes: false = true <-> "ba" = "ab" *)
  split.
  - (* Left to Right: false = true -> "ba" = "ab" *)
    intros H.
    inversion H.
  - (* Right to Left: "ba" = "ab" -> false = true *)
    intros H.
    inversion H.
Qed.