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

(* Test case: input = ["maPa"], output = false *)
Example test_palindrome_maPa : is_palindrome_spec "maPa" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "maPa" *)
  simpl.
  
  (* The goal becomes: false = true <-> "maPa" = "aPam" *)
  split.
  - (* Left to Right: false = true -> "maPa" = "aPam" *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: "maPa" = "aPam" -> false = true *)
    intros H.
    (* "maPa" = "aPam" is a contradiction because 'm' <> 'a' *)
    discriminate H.
Qed.