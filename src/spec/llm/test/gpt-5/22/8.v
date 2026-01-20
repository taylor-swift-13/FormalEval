Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Parameter z_as_int : Z -> int.
Parameters a_1000000 a_neg1000000 a_real a_str1 a_str2 a_list : Any.
Axiom IsInt_a_1000000 : IsInt a_1000000 (z_as_int 1000000%Z).
Axiom IsInt_a_neg1000000 : IsInt a_neg1000000 (z_as_int (-1000000)%Z).
Axiom NotInt_a_real : forall n, ~ IsInt a_real n.
Axiom NotInt_a_str1 : forall n, ~ IsInt a_str1 n.
Axiom NotInt_a_str2 : forall n, ~ IsInt a_str2 n.
Axiom NotInt_a_list : forall n, ~ IsInt a_list n.

Example test_case_new:
  filter_integers_spec
    [a_1000000; a_neg1000000; a_real; a_str1; a_str2; a_list]
    [z_as_int 1000000%Z; z_as_int (-1000000)%Z].
Proof.
  unfold filter_integers_spec.
  econstructor; [apply IsInt_a_1000000|].
  econstructor; [apply IsInt_a_neg1000000|].
  econstructor; [apply NotInt_a_real|].
  econstructor; [apply NotInt_a_str1|].
  econstructor; [apply NotInt_a_str2|].
  econstructor; [apply NotInt_a_list|].
  constructor.
Qed.