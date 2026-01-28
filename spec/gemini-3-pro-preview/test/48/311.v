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

(* Test case: input = ["12zZ2@@@@!@3TacoTacogeese cEvil is a namf12zZ2@@@man,Ae of a foeman, as I live.a no@tj Z d3!@@@2Zz21"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "12zZ2@@@@!@3TacoTacogeese cEvil is a namf12zZ2@@@man,Ae of a foeman, as I live.a no@tj Z d3!@@@2Zz21" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    inversion H.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Evaluate string_rev to reveal the mismatch *)
    vm_compute in H.
    (* The hypothesis H is now an equality between two distinct strings, which is a contradiction *)
    inversion H.
Qed.