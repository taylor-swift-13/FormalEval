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

Parameters v7 v9a v9b nv1 nv2 nv3 nv4 nv5 nv6 nv7 : Any.
Parameters i7 i9 : int.
Axiom IsInt_v7 : IsInt v7 i7.
Axiom IsInt_v9a : IsInt v9a i9.
Axiom IsInt_v9b : IsInt v9b i9.
Axiom NonInt_nv1 : forall n, ~ IsInt nv1 n.
Axiom NonInt_nv2 : forall n, ~ IsInt nv2 n.
Axiom NonInt_nv3 : forall n, ~ IsInt nv3 n.
Axiom NonInt_nv4 : forall n, ~ IsInt nv4 n.
Axiom NonInt_nv5 : forall n, ~ IsInt nv5 n.
Axiom NonInt_nv6 : forall n, ~ IsInt nv6 n.
Axiom NonInt_nv7 : forall n, ~ IsInt nv7 n.

Example test_case: filter_integers_spec
  [v7; nv1; nv2; nv3; nv4; nv5; v9a; v9b; nv6; nv7]
  [i7; i9; i9].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v7|].
  eapply fir_cons_nonint; [apply NonInt_nv1|].
  eapply fir_cons_nonint; [apply NonInt_nv2|].
  eapply fir_cons_nonint; [apply NonInt_nv3|].
  eapply fir_cons_nonint; [apply NonInt_nv4|].
  eapply fir_cons_nonint; [apply NonInt_nv5|].
  eapply fir_cons_int; [apply IsInt_v9a|].
  eapply fir_cons_int; [apply IsInt_v9b|].
  eapply fir_cons_nonint; [apply NonInt_nv6|].
  eapply fir_cons_nonint; [apply NonInt_nv7|].
  apply fir_nil.
Qed.