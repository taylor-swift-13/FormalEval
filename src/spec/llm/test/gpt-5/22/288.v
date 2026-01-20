Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameters v1 nv1 v2 nv2 nv3 nv4 v3 v4 : Any.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom NonInt_nv1 : forall n, ~ IsInt nv1 n.
Axiom IsInt_v2 : IsInt v2 8%Z.
Axiom NonInt_nv2 : forall n, ~ IsInt nv2 n.
Axiom NonInt_nv3 : forall n, ~ IsInt nv3 n.
Axiom NonInt_nv4 : forall n, ~ IsInt nv4 n.
Axiom IsInt_v3 : IsInt v3 9%Z.
Axiom IsInt_v4 : IsInt v4 9%Z.

Example test_case_mixed: filter_integers_spec [v1; nv1; v2; nv2; nv3; nv4; v3; v4] [1%Z; 8%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v1|].
  eapply fir_cons_nonint; [apply NonInt_nv1|].
  eapply fir_cons_int; [apply IsInt_v2|].
  eapply fir_cons_nonint; [apply NonInt_nv2|].
  eapply fir_cons_nonint; [apply NonInt_nv3|].
  eapply fir_cons_nonint; [apply NonInt_nv4|].
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_int; [apply IsInt_v4|].
  apply fir_nil.
Qed.