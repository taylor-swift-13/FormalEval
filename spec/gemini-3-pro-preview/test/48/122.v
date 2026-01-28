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

(* Test case: input = ["Evil"], output = false *)
Example test_palindrome_evil : is_palindrome_spec "Evil" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Evil" to "livE" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Evil" = "livE" *)
  split.
  - (* Left to Right: false = true -> "Evil" = "livE" *)
    intros H.
    (* Use discriminate to show that false <> true *)
    discriminate H.
  - (* Right to Left: "Evil" = "livE" -> false = true *)
    intros H.
    (* Use discriminate to show that "Evil" <> "livE" *)
    discriminate H.
Qed.