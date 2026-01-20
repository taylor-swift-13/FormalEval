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

Parameter v1 vfalse v2 v3a vfour v3b v55 v6 vseven vstr8a v9 vstr8b : Any.
Axiom H_v1 : IsInt v1 1%Z.
Axiom H_vfalse : forall n, ~ IsInt vfalse n.
Axiom H_v2 : IsInt v2 2%Z.
Axiom H_v3a : IsInt v3a 3%Z.
Axiom H_vfour : forall n, ~ IsInt vfour n.
Axiom H_v3b : IsInt v3b 3%Z.
Axiom H_v55 : forall n, ~ IsInt v55 n.
Axiom H_v6 : IsInt v6 6%Z.
Axiom H_vseven : forall n, ~ IsInt vseven n.
Axiom H_vstr8a : forall n, ~ IsInt vstr8a n.
Axiom H_v9 : forall n, ~ IsInt v9 n.
Axiom H_vstr8b : forall n, ~ IsInt vstr8b n.

Example test_case_mixed: filter_integers_spec [v1; vfalse; v2; v3a; vfour; v3b; v55; v6; vseven; vstr8a; v9; vstr8b] [1%Z; 2%Z; 3%Z; 3%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H_v1|].
  eapply fir_cons_nonint; [apply H_vfalse|].
  eapply fir_cons_int; [apply H_v2|].
  eapply fir_cons_int; [apply H_v3a|].
  eapply fir_cons_nonint; [apply H_vfour|].
  eapply fir_cons_int; [apply H_v3b|].
  eapply fir_cons_nonint; [apply H_v55|].
  eapply fir_cons_int; [apply H_v6|].
  eapply fir_cons_nonint; [apply H_vseven|].
  eapply fir_cons_nonint; [apply H_vstr8a|].
  eapply fir_cons_nonint; [apply H_v9|].
  eapply fir_cons_nonint; [apply H_vstr8b|].
  constructor.
Qed.