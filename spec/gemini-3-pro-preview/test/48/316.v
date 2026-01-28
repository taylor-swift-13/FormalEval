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

(* Test case: input = ["l.a"], output = false *)
Example test_palindrome_la : is_palindrome_spec "l.a" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "l.a" *)
  simpl.
  
  (* The goal becomes: false = true <-> "l.a" = "a.l" *)
  split.
  - (* Left to Right: false = true -> "l.a" = "a.l" *)
    intros H.
    discriminate.
  - (* Right to Left: "l.a" = "a.l" -> false = true *)
    intros H.
    discriminate.
Qed.