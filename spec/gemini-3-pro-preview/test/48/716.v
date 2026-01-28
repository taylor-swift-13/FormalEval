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

(* Test case: input = ["saw?12@zZ2@@@@!3j  nama321"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "saw?12@zZ2@@@@!3j  nama321" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    inversion H.
  - (* Right to Left: ... = ... -> false = true *)
    intros H.
    simpl in H.
    discriminate.
Qed.