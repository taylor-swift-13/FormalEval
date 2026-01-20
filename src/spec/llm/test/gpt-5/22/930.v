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

Parameters v0 v2 v5 vstr3 v4 vreal vlist vdict vtrue1 vtrue2 v2b : Any.
Parameters n0 n2 n5 n4 n2b : int.
Axiom IsInt_v0 : IsInt v0 n0.
Axiom IsInt_v2 : IsInt v2 n2.
Axiom IsInt_v5 : IsInt v5 n5.
Axiom IsInt_v4 : IsInt v4 n4.
Axiom IsInt_v2b : IsInt v2b n2b.
Axiom NotInt_vstr3 : forall n, ~ IsInt vstr3 n.
Axiom NotInt_vreal : forall n, ~ IsInt vreal n.
Axiom NotInt_vlist : forall n, ~ IsInt vlist n.
Axiom NotInt_vdict : forall n, ~ IsInt vdict n.
Axiom NotInt_vtrue1 : forall n, ~ IsInt vtrue1 n.
Axiom NotInt_vtrue2 : forall n, ~ IsInt vtrue2 n.

Example test_case_1:
  filter_integers_spec
    [v0; v2; v5; vstr3; v4; vreal; vlist; vdict; vtrue1; vtrue2; v2b]
    [n0; n2; n5; n4; n2b].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0|].
  eapply fir_cons_int; [apply IsInt_v2|].
  eapply fir_cons_int; [apply IsInt_v5|].
  eapply fir_cons_nonint; [apply NotInt_vstr3|].
  eapply fir_cons_int; [apply IsInt_v4|].
  eapply fir_cons_nonint; [apply NotInt_vreal|].
  eapply fir_cons_nonint; [apply NotInt_vlist|].
  eapply fir_cons_nonint; [apply NotInt_vdict|].
  eapply fir_cons_nonint; [apply NotInt_vtrue1|].
  eapply fir_cons_nonint; [apply NotInt_vtrue2|].
  eapply fir_cons_int; [apply IsInt_v2b|].
  constructor.
Qed.