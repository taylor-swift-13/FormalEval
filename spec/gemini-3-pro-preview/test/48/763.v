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

(* Test case: input = ["A maPa canal, Pana,mano @canal12zZ2@@Aorcatgees,Panplan,Elba.amae@@!2j3jd3!@@@2Zz21, Pana.ma."], output = false *)
Example test_palindrome_complex : is_palindrome_spec "A maPa canal, Pana,mano @canal12zZ2@@Aorcatgees,Panplan,Elba.amae@@!2j3jd3!@@@2Zz21, Pana.ma." false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    vm_compute in H.
    inversion H.
Qed.