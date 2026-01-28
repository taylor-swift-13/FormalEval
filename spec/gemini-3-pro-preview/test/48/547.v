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

(* Test case: input = ["on12zZ2@@@@!3j Z d3!@@@@2Zz21"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "on12zZ2@@@@!3j Z d3!@@@@2Zz21" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: text = rev text -> false = true *)
    intros H.
    (* Compute the reverse to expose the mismatch *)
    compute in H.
    (* The string starts with "o" but the reverse starts with "1", so they are distinct *)
    discriminate H.
Qed.