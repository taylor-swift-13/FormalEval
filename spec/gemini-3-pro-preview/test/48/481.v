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

(* Test case: input = ["A man, a plan, a erec2notjaisnral,  Pa12zZ2@@@@!a@3Evil is a name of a foeman, as I d3!@@@SSzz21live.Taco notj  d3!@@@2Zz21nama."], output = false *)
Example test_palindrome_complex : is_palindrome_spec "A man, a plan, a erec2notjaisnral,  Pa12zZ2@@@@!a@3Evil is a name of a foeman, as I d3!@@@SSzz21live.Taco notj  d3!@@@2Zz21nama." false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    vm_compute in H.
    discriminate.
Qed.