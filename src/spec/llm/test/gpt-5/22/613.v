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

Parameter v0 v2 vstr v4 vreal vlist vset vtrue vfalse : Any.
Parameter n0 n2 n4 : int.

Axiom H_v0 : IsInt v0 n0.
Axiom H_v2 : IsInt v2 n2.
Axiom H_v4 : IsInt v4 n4.
Axiom H_vstr : forall n, ~ IsInt vstr n.
Axiom H_vreal : forall n, ~ IsInt vreal n.
Axiom H_vlist : forall n, ~ IsInt vlist n.
Axiom H_vset : forall n, ~ IsInt vset n.
Axiom H_vtrue : forall n, ~ IsInt vtrue n.
Axiom H_vfalse : forall n, ~ IsInt vfalse n.

Example test_case_mixed: filter_integers_spec [v0; v2; vstr; v4; vreal; vlist; vset; vtrue; vfalse] [n0; n2; n4].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v0 n0); [apply H_v0|].
  apply (fir_cons_int v2 n2); [apply H_v2|].
  apply (fir_cons_nonint vstr); [apply H_vstr|].
  apply (fir_cons_int v4 n4); [apply H_v4|].
  apply (fir_cons_nonint vreal); [apply H_vreal|].
  apply (fir_cons_nonint vlist); [apply H_vlist|].
  apply (fir_cons_nonint vset); [apply H_vset|].
  apply (fir_cons_nonint vtrue); [apply H_vtrue|].
  apply (fir_cons_nonint vfalse); [apply H_vfalse|].
  constructor.
Qed.