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

(* Test case: input = ["Was it a car or a cat "], output = false *)
Example test_palindrome_complex : is_palindrome_spec "Was it a car or a cat " false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "Was..." = string_rev "Was..." *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* Premise is false *)
    discriminate.
  - (* Right to Left: "Was..." = string_rev "Was..." -> false = true *)
    intros H.
    (* Evaluate the string reversal *)
    compute in H.
    (* The strings are different ("Was..." vs " tac..."), so H is false *)
    discriminate.
Qed.