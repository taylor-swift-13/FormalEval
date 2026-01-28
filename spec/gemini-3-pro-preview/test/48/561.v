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

(* Test case: input = ["12zZ12"], output = false *)
Example test_palindrome_12zZ12 : is_palindrome_spec "12zZ12" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "12zZ12" *)
  simpl.
  
  (* The goal becomes: false = true <-> "12zZ12" = "21Zz21" *)
  split.
  - (* Left to Right: false = true -> "12zZ12" = "21Zz21" *)
    intros H.
    discriminate.
  - (* Right to Left: "12zZ12" = "21Zz21" -> false = true *)
    intros H.
    discriminate.
Qed.