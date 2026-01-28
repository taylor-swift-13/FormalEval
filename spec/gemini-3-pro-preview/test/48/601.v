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

(* Test case: input = ["ld3!Z@@@2Zz21nama.l.a"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "ld3!Z@@@2Zz21nama.l.a" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev for the specific input *)
  simpl.
  
  (* The goal becomes: false = true <-> "..." = "..." *)
  split.
  - (* Left to Right: false = true -> ... (contradiction) *)
    intros H.
    discriminate H.
  - (* Right to Left: "..." = "..." -> false = true (contradiction on string equality) *)
    intros H.
    discriminate H.
Qed.