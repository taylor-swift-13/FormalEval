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

(* Test case: input = ["a12zZ2geeseaea@@@@z!3Tacoman,aLL"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "a12zZ2geeseaea@@@@z!3Tacoman,aLL" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "..." = "..." *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    inversion H.
  - (* Right to Left: "..." = "..." -> false = true *)
    intros H.
    (* Simplify the string reversal *)
    simpl in H.
    (* The strings are different, so H is a contradiction *)
    discriminate.
Qed.