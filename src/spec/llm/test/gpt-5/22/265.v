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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Axiom v1_is_int : IsInt v1 1%Z.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom v3_is_int : IsInt v3 4%Z.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom v7_is_int : IsInt v7 1%Z.
Axiom v8_is_int : IsInt v8 4%Z.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [1%Z; 4%Z; 1%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_is_int |].
  eapply fir_cons_nonint; [apply v2_nonint |].
  eapply fir_cons_int; [apply v3_is_int |].
  eapply fir_cons_nonint; [apply v4_nonint |].
  eapply fir_cons_nonint; [apply v5_nonint |].
  eapply fir_cons_nonint; [apply v6_nonint |].
  eapply fir_cons_int; [apply v7_is_int |].
  eapply fir_cons_int; [apply v8_is_int |].
  constructor.
Qed.