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

Parameter v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.

Axiom IsInt_v0_0 : IsInt v0 0%Z.
Axiom IsInt_v1_2 : IsInt v1 2%Z.
Axiom IsInt_v3_4 : IsInt v3 4%Z.

Axiom NonInt_v2 : forall n, ~ IsInt v2 n.
Axiom NonInt_v4 : forall n, ~ IsInt v4 n.
Axiom NonInt_v5 : forall n, ~ IsInt v5 n.
Axiom NonInt_v6 : forall n, ~ IsInt v6 n.
Axiom NonInt_v7 : forall n, ~ IsInt v7 n.
Axiom NonInt_v8 : forall n, ~ IsInt v8 n.
Axiom NonInt_v9 : forall n, ~ IsInt v9 n.

Example test_case_new: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9] [0%Z; 2%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0_0|].
  eapply fir_cons_int; [apply IsInt_v1_2|].
  eapply fir_cons_nonint; [apply NonInt_v2|].
  eapply fir_cons_int; [apply IsInt_v3_4|].
  eapply fir_cons_nonint; [apply NonInt_v4|].
  eapply fir_cons_nonint; [apply NonInt_v5|].
  eapply fir_cons_nonint; [apply NonInt_v6|].
  eapply fir_cons_nonint; [apply NonInt_v7|].
  eapply fir_cons_nonint; [apply NonInt_v8|].
  eapply fir_cons_nonint; [apply NonInt_v9|].
  constructor.
Qed.