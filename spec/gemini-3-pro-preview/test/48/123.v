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

(* Test case: input = ["A man, a plan, geesea canal: Panama"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "A man, a plan, geesea canal: Panama" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "..." = string_rev "..." *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: ... -> false = true *)
    intros H.
    (* Evaluate string_rev to compare the literal strings *)
    compute in H.
    (* The strings are distinct, so the equality hypothesis is a contradiction *)
    discriminate.
Qed.