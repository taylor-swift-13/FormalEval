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

(* Test case: input = ["d3!@@@2 ord3!a@@@2Zz21oeman,Able wliveas I ere I saw Elba.name1"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "d3!@@@2 ord3!a@@@2Zz21oeman,Able wliveas I ere I saw Elba.name1" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    vm_compute in H.
    discriminate H.
Qed.