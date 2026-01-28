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

(* Test case: input = ["abbc"], output = false *)
Example test_palindrome_abbc : is_palindrome_spec "abbc" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "abbc" *)
  simpl.
  
  (* The goal becomes: false = true <-> "abbc" = "cbba" *)
  split.
  - (* Left to Right: false = true -> "abbc" = "cbba" *)
    intros H.
    discriminate H.
  - (* Right to Left: "abbc" = "cbba" -> false = true *)
    intros H.
    discriminate H.
Qed.