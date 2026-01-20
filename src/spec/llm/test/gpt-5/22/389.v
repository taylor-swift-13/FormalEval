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

Require Import Coq.ZArith.ZArith.

Parameter inj : Z -> int.
Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Any.
Axiom H_v1 : IsInt v1 (inj 1%Z).
Axiom H_v2 : forall n, ~ IsInt v2 n.
Axiom H_v3 : forall n, ~ IsInt v3 n.
Axiom H_v4 : IsInt v4 (inj 8%Z).
Axiom H_v5 : IsInt v5 (inj 8%Z).
Axiom H_v6 : forall n, ~ IsInt v6 n.
Axiom H_v7 : IsInt v7 (inj 9%Z).
Axiom H_v8 : IsInt v8 (inj 9%Z).
Axiom H_v9 : forall n, ~ IsInt v9 n.
Axiom H_v10 : forall n, ~ IsInt v10 n.
Axiom H_v11 : forall n, ~ IsInt v11 n.

Example test_case_new:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11]
    [inj 1%Z; inj 8%Z; inj 8%Z; inj 9%Z; inj 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H_v1 |].
  eapply fir_cons_nonint; [apply H_v2 |].
  eapply fir_cons_nonint; [apply H_v3 |].
  eapply fir_cons_int; [apply H_v4 |].
  eapply fir_cons_int; [apply H_v5 |].
  eapply fir_cons_nonint; [apply H_v6 |].
  eapply fir_cons_int; [apply H_v7 |].
  eapply fir_cons_int; [apply H_v8 |].
  eapply fir_cons_nonint; [apply H_v9 |].
  eapply fir_cons_nonint; [apply H_v10 |].
  eapply fir_cons_nonint; [apply H_v11 |].
  constructor.
Qed.