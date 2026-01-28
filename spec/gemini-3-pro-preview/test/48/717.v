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

(* Test case: input = ["PanPana,manoamano"], output = false *)
Example test_palindrome_fail : is_palindrome_spec "PanPana,manoamano" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "PanPana,manoamano" = string_rev "PanPana,manoamano" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: ... -> false = true *)
    intros H.
    (* Simplify the reversed string in the hypothesis *)
    simpl in H.
    (* The hypothesis is now an equality between two different strings, which is a contradiction *)
    discriminate.
Qed.