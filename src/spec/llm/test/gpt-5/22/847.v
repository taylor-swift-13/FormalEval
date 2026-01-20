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

Parameters (v2 v3 vfour v5p5 v5 vseven v8str v9p0a v9p0b v2b : Any).
Parameters (i2 i3 i5 i2' : int).
Axiom H1 : IsInt v2 i2.
Axiom H2 : IsInt v3 i3.
Axiom H3 : forall n, ~ IsInt vfour n.
Axiom H4 : forall n, ~ IsInt v5p5 n.
Axiom H5 : IsInt v5 i5.
Axiom H6 : forall n, ~ IsInt vseven n.
Axiom H7 : forall n, ~ IsInt v8str n.
Axiom H8 : forall n, ~ IsInt v9p0a n.
Axiom H9 : forall n, ~ IsInt v9p0b n.
Axiom H10 : IsInt v2b i2'.

Example test_case_mixed:
  filter_integers_spec
    [v2; v3; vfour; v5p5; v5; vseven; v8str; v9p0a; v9p0b; v2b]
    [i2; i3; i5; i2'].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_nonint; [apply H3|].
  eapply fir_cons_nonint; [apply H4|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply H6|].
  eapply fir_cons_nonint; [apply H7|].
  eapply fir_cons_nonint; [apply H8|].
  eapply fir_cons_nonint; [apply H9|].
  eapply fir_cons_int; [apply H10|].
  constructor.
Qed.