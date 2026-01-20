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

Parameters v0 v2 vstr3 v4 v56 vnil vobj1 vtrue vfalse vobj2 : Any.
Parameters n0 n2 n4 : int.

Axiom IsInt_v0 : IsInt v0 n0.
Axiom IsInt_v2 : IsInt v2 n2.
Axiom IsInt_v4 : IsInt v4 n4.
Axiom NotInt_vstr3 : forall n, ~ IsInt vstr3 n.
Axiom NotInt_v56 : forall n, ~ IsInt v56 n.
Axiom NotInt_vnil : forall n, ~ IsInt vnil n.
Axiom NotInt_vobj1 : forall n, ~ IsInt vobj1 n.
Axiom NotInt_vtrue : forall n, ~ IsInt vtrue n.
Axiom NotInt_vfalse : forall n, ~ IsInt vfalse n.
Axiom NotInt_vobj2 : forall n, ~ IsInt vobj2 n.

Example test_case_mixed: filter_integers_spec [v0; v2; vstr3; v4; v56; vnil; vobj1; vtrue; vfalse; vobj2] [n0; n2; n4].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0 |].
  eapply fir_cons_int; [apply IsInt_v2 |].
  eapply fir_cons_nonint; [apply NotInt_vstr3 |].
  eapply fir_cons_int; [apply IsInt_v4 |].
  eapply fir_cons_nonint; [apply NotInt_v56 |].
  eapply fir_cons_nonint; [apply NotInt_vnil |].
  eapply fir_cons_nonint; [apply NotInt_vobj1 |].
  eapply fir_cons_nonint; [apply NotInt_vtrue |].
  eapply fir_cons_nonint; [apply NotInt_vfalse |].
  eapply fir_cons_nonint; [apply NotInt_vobj2 |].
  apply fir_nil.
Qed.