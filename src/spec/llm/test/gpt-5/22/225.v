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

Parameter i10 i9 : int.
Notation "10%Z" := i10.
Notation "9%Z" := i9.

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Any.

Definition complex_input : list Any :=
  [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12].

Axiom IsInt_v1 : IsInt v1 10%Z.
Axiom NotInt_v2 : forall n, ~ IsInt v2 n.
Axiom NotInt_v3 : forall n, ~ IsInt v3 n.
Axiom NotInt_v4 : forall n, ~ IsInt v4 n.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.
Axiom IsInt_v6 : IsInt v6 9%Z.
Axiom IsInt_v7 : IsInt v7 9%Z.
Axiom NotInt_v8 : forall n, ~ IsInt v8 n.
Axiom NotInt_v9 : forall n, ~ IsInt v9 n.
Axiom NotInt_v10 : forall n, ~ IsInt v10 n.
Axiom IsInt_v11 : IsInt v11 9%Z.
Axiom NotInt_v12 : forall n, ~ IsInt v12 n.

Example test_case_complex: filter_integers_spec complex_input [10%Z; 9%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_v1|].
  eapply fir_cons_nonint; [exact NotInt_v2|].
  eapply fir_cons_nonint; [exact NotInt_v3|].
  eapply fir_cons_nonint; [exact NotInt_v4|].
  eapply fir_cons_nonint; [exact NotInt_v5|].
  eapply fir_cons_int; [exact IsInt_v6|].
  eapply fir_cons_int; [exact IsInt_v7|].
  eapply fir_cons_nonint; [exact NotInt_v8|].
  eapply fir_cons_nonint; [exact NotInt_v9|].
  eapply fir_cons_nonint; [exact NotInt_v10|].
  eapply fir_cons_int; [exact IsInt_v11|].
  eapply fir_cons_nonint; [exact NotInt_v12|].
  apply fir_nil.
Qed.