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

(* Test case: input = ["A man, a plan, geesea canal:a Panamaco"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "A man, a plan, geesea canal:a Panamaco" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> text = string_rev text *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Simplify the equality in the hypothesis to reveal the mismatch *)
    simpl in H.
    (* The string starts with 'A' but the reverse starts with 'o', so they are not equal *)
    discriminate.
Qed.