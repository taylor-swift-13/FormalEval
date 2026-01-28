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

(* Test case: input = ["Dd3!@@@212ozZ2@@@@A man, a plZan, a erecaisnral,  Pa12zZ2@@@@!@3Taco notj  d3!@@@2Zz21nama.!@3Taco 12zZ2@@@@!@3Taco2notj  d3!@@@2DoZz21DoZz21o"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "Dd3!@@@212ozZ2@@@@A man, a plZan, a erecaisnral,  Pa12zZ2@@@@!@3Taco notj  d3!@@@2Zz21nama.!@3Taco 12zZ2@@@@!@3Taco2notj  d3!@@@2DoZz21DoZz21o" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: text = rev text -> false = true *)
    intros H.
    compute in H.
    discriminate.
Qed.