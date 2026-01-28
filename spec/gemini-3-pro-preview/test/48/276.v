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

(* Test case: input = ["A man..."], output = false *)
Example test_palindrome_complex : 
  is_palindrome_spec "A man,Taco cEvil i12zZ2@@@@!@3Tacos a name of a foeman, as I live.at a plaStep on no pets, geesea canal: Panama" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Evaluate the reversal to expose the mismatch at the first character ('A' vs 'a') *)
    vm_compute in H.
    inversion H.
Qed.