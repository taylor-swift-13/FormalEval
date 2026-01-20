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

Parameter one nine : int.
Notation "1%Z" := one.
Notation "9%Z" := nine.

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom NotInt_v2 : forall n, ~ IsInt v2 n.
Axiom NotInt_v3 : forall n, ~ IsInt v3 n.
Axiom NotInt_v4 : forall n, ~ IsInt v4 n.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.
Axiom IsInt_v6 : IsInt v6 9%Z.
Axiom IsInt_v7 : IsInt v7 1%Z.
Axiom IsInt_v8 : IsInt v8 1%Z.
Axiom IsInt_v9 : IsInt v9 9%Z.

Example test_case_new:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9]
    [1%Z; 9%Z; 1%Z; 1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_v1|].
  eapply fir_cons_nonint; [exact NotInt_v2|].
  eapply fir_cons_nonint; [exact NotInt_v3|].
  eapply fir_cons_nonint; [exact NotInt_v4|].
  eapply fir_cons_nonint; [exact NotInt_v5|].
  eapply fir_cons_int; [exact IsInt_v6|].
  eapply fir_cons_int; [exact IsInt_v7|].
  eapply fir_cons_int; [exact IsInt_v8|].
  eapply fir_cons_int; [exact IsInt_v9|].
  constructor.
Qed.