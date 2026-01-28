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

(* Test case: input = ["12@zZ12zZ2@@@@!3j  12zZ2@@j@@!j3jd3!@@@2Zz212@@@@!3j  12zZ2a21"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "12@zZ12zZ2@@@@!3j  12zZ2@@j@@!j3jd3!@@@2Zz212@@@@!3j  12zZ2a21" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    vm_compute in H.
    (* The string differs from its reverse at index 2 ('@' vs 'a') *)
    (* Peel off the first two matching characters *)
    injection H as _ H.
    injection H as _ H.
    (* Extract the mismatching character equality *)
    injection H as Hc _.
    (* Inversion on distinct ASCII characters derives a contradiction *)
    inversion Hc.
Qed.