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

Parameter vf1 vf2 vnone vreal v5 vm7 v0 va vb1 vlist1 vlist2 vset vdict vlist34 vb2 : Any.
Parameter n5 nm7 n0 : int.

Axiom H_vf1_nonint : forall n, ~ IsInt vf1 n.
Axiom H_vf2_nonint : forall n, ~ IsInt vf2 n.
Axiom H_vnone_nonint : forall n, ~ IsInt vnone n.
Axiom H_vreal_nonint : forall n, ~ IsInt vreal n.
Axiom H_v5_int : IsInt v5 n5.
Axiom H_vm7_int : IsInt vm7 nm7.
Axiom H_v0_int : IsInt v0 n0.
Axiom H_va_nonint : forall n, ~ IsInt va n.
Axiom H_vb1_nonint : forall n, ~ IsInt vb1 n.
Axiom H_vlist1_nonint : forall n, ~ IsInt vlist1 n.
Axiom H_vlist2_nonint : forall n, ~ IsInt vlist2 n.
Axiom H_vset_nonint : forall n, ~ IsInt vset n.
Axiom H_vdict_nonint : forall n, ~ IsInt vdict n.
Axiom H_vlist34_nonint : forall n, ~ IsInt vlist34 n.
Axiom H_vb2_nonint : forall n, ~ IsInt vb2 n.

Example test_case_mixed:
  filter_integers_spec
    [vf1; vf2; vnone; vreal; v5; vm7; v0; va; vb1; vlist1; vlist2; vset; vdict; vlist34; vb2]
    [n5; nm7; n0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H_vf1_nonint|].
  eapply fir_cons_nonint; [apply H_vf2_nonint|].
  eapply fir_cons_nonint; [apply H_vnone_nonint|].
  eapply fir_cons_nonint; [apply H_vreal_nonint|].
  eapply fir_cons_int; [apply H_v5_int|].
  eapply fir_cons_int; [apply H_vm7_int|].
  eapply fir_cons_int; [apply H_v0_int|].
  eapply fir_cons_nonint; [apply H_va_nonint|].
  eapply fir_cons_nonint; [apply H_vb1_nonint|].
  eapply fir_cons_nonint; [apply H_vlist1_nonint|].
  eapply fir_cons_nonint; [apply H_vlist2_nonint|].
  eapply fir_cons_nonint; [apply H_vset_nonint|].
  eapply fir_cons_nonint; [apply H_vdict_nonint|].
  eapply fir_cons_nonint; [apply H_vlist34_nonint|].
  eapply fir_cons_nonint; [apply H_vb2_nonint|].
  constructor.
Qed.