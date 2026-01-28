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

(* Test case: input = ["Able zw12zzZ2@@j@@!j3jd3!@@@2Zz21re Iba."], output = false *)
Example test_palindrome_complex : is_palindrome_spec "Able zw12zzZ2@@j@@!j3jd3!@@@2Zz21re Iba." false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    vm_compute in H.
    discriminate.
Qed.