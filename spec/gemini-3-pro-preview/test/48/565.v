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

(* Test case: input = ["man,ATacoge12zZ2geeseaea@@@@!3Tacoman,efoemord3!@@@2Zz21oeman,AAblean,sea"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "man,ATacoge12zZ2geeseaea@@@@!3Tacoman,efoemord3!@@@2Zz21oeman,AAblean,sea" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    simpl in H.
    discriminate.
Qed.