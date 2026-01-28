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

(* Test case: input = ["12zZaA man,Taco cEvil i12zZ2@@@@!@3Tacos a name of a foeman, as I live.at a plannWA man, a pmlan, a erecaisnral,  Panama.sLmxhink, geesea canal: PanamaTcaco"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "12zZaA man,Taco cEvil i12zZ2@@@@!@3Tacos a name of a foeman, as I live.at a plannWA man, a pmlan, a erecaisnral,  Panama.sLmxhink, geesea canal: PanamaTcaco" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> text = string_rev text *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Compute the reverse string to show inequality *)
    vm_compute in H.
    discriminate.
Qed.