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

(* Test case: input = ["12zZ2@@j@@!j3jd3!@@@2Zz212@@@@lieveA man, a plan, Pa cacnal, Pana.ma..!3j"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "12zZ2@@j@@!j3jd3!@@@2Zz212@@@@lieveA man, a plan, Pa cacnal, Pana.ma..!3j" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    assert (Hneq: "12zZ2@@j@@!j3jd3!@@@2Zz212@@@@lieveA man, a plan, Pa cacnal, Pana.ma..!3j" <> string_rev "12zZ2@@j@@!j3jd3!@@@2Zz212@@@@lieveA man, a plan, Pa cacnal, Pana.ma..!3j").
    {
      vm_compute.
      intros contra.
      discriminate contra.
    }
    contradiction.
Qed.