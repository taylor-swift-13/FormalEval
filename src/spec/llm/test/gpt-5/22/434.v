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

Parameter v1 v2 v3 v4 v5 v6 v7 : Any.
Axiom v1_is_int : IsInt v1 1%Z.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom v3_is_int : IsInt v3 0%Z.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom v7_is_int : IsInt v7 8%Z.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [1%Z; 0%Z; 8%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact v1_is_int|].
  eapply fir_cons_nonint; [exact v2_nonint|].
  eapply fir_cons_int; [exact v3_is_int|].
  eapply fir_cons_nonint; [exact v4_nonint|].
  eapply fir_cons_nonint; [exact v5_nonint|].
  eapply fir_cons_nonint; [exact v6_nonint|].
  eapply fir_cons_int; [exact v7_is_int|].
  constructor.
Qed.