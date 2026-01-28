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

(* Test case: input = ["EvTaco cEvil is a name of a foeman, as I live.atil is a nam12zZ2@@@@!3Taco noca?ttj  d3!parssaw?@@@2Zz21e ofoeman, as I live.Tacat"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "EvTaco cEvil is a name of a foeman, as I live.atil is a nam12zZ2@@@@!3Taco noca?ttj  d3!parssaw?@@@2Zz21e ofoeman, as I live.Tacat" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    vm_compute in H.
    discriminate.
Qed.