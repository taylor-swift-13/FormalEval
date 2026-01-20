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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Any.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v2 : IsInt v2 (-8)%Z.
Axiom IsInt_v3 : IsInt v3 4%Z.
Axiom NotInt_v4 : forall n, ~ IsInt v4 n.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.
Axiom NotInt_v6 : forall n, ~ IsInt v6 n.
Axiom NotInt_v7 : forall n, ~ IsInt v7 n.
Axiom IsInt_v8 : IsInt v8 31%Z.
Axiom IsInt_v9 : IsInt v9 0%Z.
Axiom NotInt_v10 : forall n, ~ IsInt v10 n.
Axiom NotInt_v11 : forall n, ~ IsInt v11 n.
Axiom IsInt_v12 : IsInt v12 4%Z.

Example test_case_empty:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12]
    [1%Z; (-8)%Z; 4%Z; 31%Z; 0%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v1 |].
  eapply fir_cons_int; [apply IsInt_v2 |].
  eapply fir_cons_int; [apply IsInt_v3 |].
  eapply fir_cons_nonint; [apply NotInt_v4 |].
  eapply fir_cons_nonint; [apply NotInt_v5 |].
  eapply fir_cons_nonint; [apply NotInt_v6 |].
  eapply fir_cons_nonint; [apply NotInt_v7 |].
  eapply fir_cons_int; [apply IsInt_v8 |].
  eapply fir_cons_int; [apply IsInt_v9 |].
  eapply fir_cons_nonint; [apply NotInt_v10 |].
  eapply fir_cons_nonint; [apply NotInt_v11 |].
  eapply fir_cons_int; [apply IsInt_v12 |].
  constructor.
Qed.