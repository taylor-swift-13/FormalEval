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

(* Test case: input = [",PanaPanasee.ma.tsma"], output = false *)
Example test_palindrome_complex : is_palindrome_spec ",PanaPanasee.ma.tsma" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> text = string_rev text *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Compute the reverse of the string in the hypothesis *)
    simpl in H.
    (* The hypothesis is now an equality between two different strings, which is false *)
    discriminate H.
Qed.