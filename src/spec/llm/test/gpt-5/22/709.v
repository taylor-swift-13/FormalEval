Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter v15 v_list23 v4 v_list56 v_empty1 v_list7_8 v_str9 v_empty2 v_empty3 v_empty4 : Any.
Axiom IsInt_v15 : IsInt v15 15%Z.
Axiom NotInt_v_list23 : forall n, ~ IsInt v_list23 n.
Axiom IsInt_v4 : IsInt v4 4%Z.
Axiom NotInt_v_list56 : forall n, ~ IsInt v_list56 n.
Axiom NotInt_v_empty1 : forall n, ~ IsInt v_empty1 n.
Axiom NotInt_v_list7_8 : forall n, ~ IsInt v_list7_8 n.
Axiom NotInt_v_str9 : forall n, ~ IsInt v_str9 n.
Axiom NotInt_v_empty2 : forall n, ~ IsInt v_empty2 n.
Axiom NotInt_v_empty3 : forall n, ~ IsInt v_empty3 n.
Axiom NotInt_v_empty4 : forall n, ~ IsInt v_empty4 n.

Example test_case_nested:
  filter_integers_spec
    [v15; v_list23; v4; v_list56; v_empty1; v_list7_8; v_str9; v_empty2; v_empty3; v_empty4]
    [15%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v15|].
  eapply fir_cons_nonint; [apply NotInt_v_list23|].
  eapply fir_cons_int; [apply IsInt_v4|].
  eapply fir_cons_nonint; [apply NotInt_v_list56|].
  eapply fir_cons_nonint; [apply NotInt_v_empty1|].
  eapply fir_cons_nonint; [apply NotInt_v_list7_8|].
  eapply fir_cons_nonint; [apply NotInt_v_str9|].
  eapply fir_cons_nonint; [apply NotInt_v_empty2|].
  eapply fir_cons_nonint; [apply NotInt_v_empty3|].
  eapply fir_cons_nonint; [apply NotInt_v_empty4|].
  apply fir_nil.
Qed.