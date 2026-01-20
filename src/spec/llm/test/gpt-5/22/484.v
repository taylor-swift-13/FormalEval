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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Parameter one four : int.
Axiom v1_int : IsInt v1 one.
Axiom v2_int : IsInt v2 one.
Axiom v4_int : IsInt v4 four.
Axiom v8_int : IsInt v8 one.
Axiom v3_nonint : forall n, ~ IsInt v3 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom v7_nonint : forall n, ~ IsInt v7 n.
Axiom v9_nonint : forall n, ~ IsInt v9 n.

Notation "1%Z" := one.
Notation "4%Z" := four.

Example test_case_new:
  filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [1%Z; 1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact v1_int |].
  eapply fir_cons_int; [exact v2_int |].
  eapply fir_cons_nonint; [exact v3_nonint |].
  eapply fir_cons_int; [exact v4_int |].
  eapply fir_cons_nonint; [exact v5_nonint |].
  eapply fir_cons_nonint; [exact v6_nonint |].
  eapply fir_cons_nonint; [exact v7_nonint |].
  eapply fir_cons_int; [exact v8_int |].
  eapply fir_cons_nonint; [exact v9_nonint |].
  constructor.
Qed.