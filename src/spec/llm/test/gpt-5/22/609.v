Require Import Coq.Lists.List.
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

Parameter v1 v2 v3 v4 v5 : Any.
Parameter n1 : int.
Axiom IsInt_v1 : IsInt v1 n1.
Axiom NotInt_v2 : forall n, ~ IsInt v2 n.
Axiom NotInt_v3 : forall n, ~ IsInt v3 n.
Axiom NotInt_v4 : forall n, ~ IsInt v4 n.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5] [n1].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v1 n1); [apply IsInt_v1|].
  apply (fir_cons_nonint v2); [apply NotInt_v2|].
  apply (fir_cons_nonint v3); [apply NotInt_v3|].
  apply (fir_cons_nonint v4); [apply NotInt_v4|].
  apply (fir_cons_nonint v5); [apply NotInt_v5|].
  constructor.
Qed.