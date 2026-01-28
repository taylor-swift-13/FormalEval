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

(* Test case: input = ["cEvilnot"], output = false *)
Example test_palindrome_cEvilnot : is_palindrome_spec "cEvilnot" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "cEvilnot" *)
  simpl.
  
  (* The goal becomes: false = true <-> "cEvilnot" = "tonlivEc" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: "cEvilnot" = "tonlivEc" -> false = true *)
    intros H.
    (* Extract equality of the first characters (c and t) *)
    injection H as Hc Hs.
    (* Inverting the equality of distinct ASCII characters yields a contradiction *)
    inversion Hc.
Qed.