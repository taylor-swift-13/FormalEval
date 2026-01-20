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

Parameter v10 v_nil1 v_complex1 v8 v_reals v_list5 v_list9_1 v9a v9b v51 v_nil2 v_list9_2 v9c v_list9_3 v9d : Any.
Parameter n10 n8 n9a n9b n51 n9c n9d : int.

Axiom IsInt_v10 : IsInt v10 n10.
Axiom IsInt_v8 : IsInt v8 n8.
Axiom IsInt_v9a : IsInt v9a n9a.
Axiom IsInt_v9b : IsInt v9b n9b.
Axiom IsInt_v51 : IsInt v51 n51.
Axiom IsInt_v9c : IsInt v9c n9c.
Axiom IsInt_v9d : IsInt v9d n9d.

Axiom NotInt_v_nil1 : forall n, ~ IsInt v_nil1 n.
Axiom NotInt_v_complex1 : forall n, ~ IsInt v_complex1 n.
Axiom NotInt_v_reals : forall n, ~ IsInt v_reals n.
Axiom NotInt_v_list5 : forall n, ~ IsInt v_list5 n.
Axiom NotInt_v_list9_1 : forall n, ~ IsInt v_list9_1 n.
Axiom NotInt_v_nil2 : forall n, ~ IsInt v_nil2 n.
Axiom NotInt_v_list9_2 : forall n, ~ IsInt v_list9_2 n.
Axiom NotInt_v_list9_3 : forall n, ~ IsInt v_list9_3 n.

Example test_case_new:
  filter_integers_spec
    [v10; v_nil1; v_complex1; v8; v_reals; v_list5; v_list9_1; v9a; v9b; v51; v_nil2; v_list9_2; v9c; v_list9_3; v9d]
    [n10; n8; n9a; n9b; n51; n9c; n9d].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v10|].
  eapply fir_cons_nonint; [apply NotInt_v_nil1|].
  eapply fir_cons_nonint; [apply NotInt_v_complex1|].
  eapply fir_cons_int; [apply IsInt_v8|].
  eapply fir_cons_nonint; [apply NotInt_v_reals|].
  eapply fir_cons_nonint; [apply NotInt_v_list5|].
  eapply fir_cons_nonint; [apply NotInt_v_list9_1|].
  eapply fir_cons_int; [apply IsInt_v9a|].
  eapply fir_cons_int; [apply IsInt_v9b|].
  eapply fir_cons_int; [apply IsInt_v51|].
  eapply fir_cons_nonint; [apply NotInt_v_nil2|].
  eapply fir_cons_nonint; [apply NotInt_v_list9_2|].
  eapply fir_cons_int; [apply IsInt_v9c|].
  eapply fir_cons_nonint; [apply NotInt_v_list9_3|].
  eapply fir_cons_int; [apply IsInt_v9d|].
  constructor.
Qed.