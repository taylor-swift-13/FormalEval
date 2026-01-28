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

(* Test case: input = ["T12zZ2Panama21acoDoe see 12zZ2@@j@@!j3jd3!@@@2Zz21Go"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "T12zZ2Panama21acoDoe see 12zZ2@@j@@!j3jd3!@@@2Zz21Go" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.

  (* The goal becomes: false = true <-> text = rev text *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: text = rev text -> false = true *)
    intros H.
    simpl in H.
    discriminate.
Qed.