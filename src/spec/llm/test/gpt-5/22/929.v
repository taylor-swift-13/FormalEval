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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Any.

Parameter z0 z2 z4 : int.
Notation "0%Z" := z0.
Notation "2%Z" := z2.
Notation "4%Z" := z4.

Axiom v1_nonint : forall n, ~ IsInt v1 n.
Axiom v2_isint : IsInt v2 0%Z.
Axiom v3_isint : IsInt v3 2%Z.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_isint : IsInt v5 4%Z.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom v7_nonint : forall n, ~ IsInt v7 n.
Axiom v8_nonint : forall n, ~ IsInt v8 n.
Axiom v9_nonint : forall n, ~ IsInt v9 n.
Axiom v10_nonint : forall n, ~ IsInt v10 n.
Axiom v11_nonint : forall n, ~ IsInt v11 n.
Axiom v12_nonint : forall n, ~ IsInt v12 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12] [0%Z; 2%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v1_nonint |].
  eapply fir_cons_int; [apply v2_isint |].
  eapply fir_cons_int; [apply v3_isint |].
  eapply fir_cons_nonint; [apply v4_nonint |].
  eapply fir_cons_int; [apply v5_isint |].
  eapply fir_cons_nonint; [apply v6_nonint |].
  eapply fir_cons_nonint; [apply v7_nonint |].
  eapply fir_cons_nonint; [apply v8_nonint |].
  eapply fir_cons_nonint; [apply v9_nonint |].
  eapply fir_cons_nonint; [apply v10_nonint |].
  eapply fir_cons_nonint; [apply v11_nonint |].
  eapply fir_cons_nonint; [apply v12_nonint |].
  constructor.
Qed.