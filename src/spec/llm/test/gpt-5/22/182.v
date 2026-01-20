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

Parameters v1 v2 v3 v4 v5 v6 : Any.
Parameters one seven : int.
Notation "1%Z" := one.
Notation "7%Z" := seven.

Axiom v1_is_int : IsInt v1 1%Z.
Axiom v2_not_int : forall n, ~ IsInt v2 n.
Axiom v3_not_int : forall n, ~ IsInt v3 n.
Axiom v4_not_int : forall n, ~ IsInt v4 n.
Axiom v5_is_int : IsInt v5 7%Z.
Axiom v6_not_int : forall n, ~ IsInt v6 n.

Example test_case_nested: filter_integers_spec [v1; v2; v3; v4; v5; v6] [1%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_is_int|].
  eapply fir_cons_nonint; [apply v2_not_int|].
  eapply fir_cons_nonint; [apply v3_not_int|].
  eapply fir_cons_nonint; [apply v4_not_int|].
  eapply fir_cons_int; [apply v5_is_int|].
  eapply fir_cons_nonint; [apply v6_not_int|].
  constructor.
Qed.