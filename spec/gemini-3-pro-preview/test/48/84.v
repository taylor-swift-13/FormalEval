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

(* Test case: input = ["reWas it a car or a catw Ir sraw?fer"], output = false *)
Example test_palindrome_complex_false : is_palindrome_spec "reWas it a car or a catw Ir sraw?fer" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "reWas..." = string_rev "reWas..." *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* false = true is a contradiction *)
    inversion H.
  - (* Right to Left: "reWas..." = string_rev "reWas..." -> false = true *)
    intros H.
    (* Simplify the reverse computation in the hypothesis *)
    simpl in H.
    (* The strings are distinct, so equality is a contradiction *)
    inversion H.
Qed.