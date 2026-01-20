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

Parameter v0 v2 v3 vfour v55 v6 vseven v8 v90 : Any.
Parameter i0 i2 i3 i6 : int.
Axiom IsInt_v0 : IsInt v0 i0.
Axiom IsInt_v2 : IsInt v2 i2.
Axiom IsInt_v3 : IsInt v3 i3.
Axiom IsInt_v6 : IsInt v6 i6.
Axiom NonInt_vfour : forall n, ~ IsInt vfour n.
Axiom NonInt_v55 : forall n, ~ IsInt v55 n.
Axiom NonInt_vseven : forall n, ~ IsInt vseven n.
Axiom NonInt_v8 : forall n, ~ IsInt v8 n.
Axiom NonInt_v90 : forall n, ~ IsInt v90 n.

Example test_case_mixed:
  filter_integers_spec
    [v0; v2; v3; vfour; v55; v6; vseven; v8; v90]
    [i0; i2; i3; i6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0 |].
  eapply fir_cons_int; [apply IsInt_v2 |].
  eapply fir_cons_int; [apply IsInt_v3 |].
  eapply fir_cons_nonint; [apply NonInt_vfour |].
  eapply fir_cons_nonint; [apply NonInt_v55 |].
  eapply fir_cons_int; [apply IsInt_v6 |].
  eapply fir_cons_nonint; [apply NonInt_vseven |].
  eapply fir_cons_nonint; [apply NonInt_v8 |].
  eapply fir_cons_nonint; [apply NonInt_v90 |].
  constructor.
Qed.