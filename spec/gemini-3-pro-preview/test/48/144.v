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

(* Test case: input = ["Taco cEvil ies a name of a foeman, as I live.a"], output = false *)
Example test_palindrome_false_long : is_palindrome_spec "Taco cEvil ies a name of a foeman, as I live.a" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "..." = "..." *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: ... -> false = true *)
    intros H.
    (* Compute the string reverse to reveal the mismatch *)
    compute in H.
    (* The strings are distinct ("T..." vs "a..."), so equality is a contradiction *)
    discriminate H.
Qed.