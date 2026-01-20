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

Parameter v2 v3 vfour v8_103551238465293R v5 vseven v8str v9_0R1 v9_0R2 vfour2 v2b : Any.
Parameter n2 n3 n5 n2b : int.

Axiom H2 : IsInt v2 n2.
Axiom H3 : IsInt v3 n3.
Axiom H5 : IsInt v5 n5.
Axiom H2b : IsInt v2b n2b.

Axiom Hfour : forall n, ~ IsInt vfour n.
Axiom H8_103 : forall n, ~ IsInt v8_103551238465293R n.
Axiom Hseven : forall n, ~ IsInt vseven n.
Axiom H8str : forall n, ~ IsInt v8str n.
Axiom H9_0R1 : forall n, ~ IsInt v9_0R1 n.
Axiom H9_0R2 : forall n, ~ IsInt v9_0R2 n.
Axiom Hfour2 : forall n, ~ IsInt vfour2 n.

Example test_case_1:
  filter_integers_spec
    [v2; v3; vfour; v8_103551238465293R; v5; vseven; v8str; v9_0R1; v9_0R2; vfour2; v2b]
    [n2; n3; n5; n2b].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H2|].
  eapply fir_cons_int; [exact H3|].
  eapply fir_cons_nonint; [exact Hfour|].
  eapply fir_cons_nonint; [exact H8_103|].
  eapply fir_cons_int; [exact H5|].
  eapply fir_cons_nonint; [exact Hseven|].
  eapply fir_cons_nonint; [exact H8str|].
  eapply fir_cons_nonint; [exact H9_0R1|].
  eapply fir_cons_nonint; [exact H9_0R2|].
  eapply fir_cons_nonint; [exact Hfour2|].
  eapply fir_cons_int; [exact H2b|].
  apply fir_nil.
Qed.