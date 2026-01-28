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

(* Test case: input = ["A man, a plan, a canali.lve.a.tl, Panama."], output = false *)
Example test_palindrome_complex : is_palindrome_spec "A man, a plan, a canali.lve.a.tl, Panama." false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    (* Evaluate the string reversal to expose the mismatch *)
    compute in H.
    (* The string starts with 'A' while the reverse starts with '.', so they are not equal *)
    discriminate H.
Qed.