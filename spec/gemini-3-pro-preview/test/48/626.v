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

(* Test case: input = ["12zZ2@@@@!3j  12zZ2@@@@!j3jd3!@@@2Zz21"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "12zZ2@@@@!3j  12zZ2@@@@!j3jd3!@@@2Zz21" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.

  (* The goal becomes: false = true <-> text = string_rev text *)
  split.
  - (* Left to Right: false = true -> text = string_rev text *)
    intros H.
    (* Contradiction: false is not equal to true *)
    inversion H.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Compute the reversed string to expose the difference *)
    vm_compute in H.
    (* The strings are distinct, so equality is impossible *)
    discriminate.
Qed.