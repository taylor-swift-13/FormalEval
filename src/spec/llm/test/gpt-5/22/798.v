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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Any.
Axiom HInt_v1 : IsInt v1 1%Z.
Axiom HNon_v2 : forall n, ~ IsInt v2 n.
Axiom HInt_v3 : IsInt v3 2%Z.
Axiom HNon_v4 : forall n, ~ IsInt v4 n.
Axiom HNon_v5 : forall n, ~ IsInt v5 n.
Axiom HNon_v6 : forall n, ~ IsInt v6 n.
Axiom HNon_v7 : forall n, ~ IsInt v7 n.
Axiom HNon_v8 : forall n, ~ IsInt v8 n.
Axiom HNon_v9 : forall n, ~ IsInt v9 n.
Axiom HNon_v10 : forall n, ~ IsInt v10 n.
Axiom HNon_v11 : forall n, ~ IsInt v11 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] [1%Z; 2%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact HInt_v1|].
  eapply fir_cons_nonint; [exact HNon_v2|].
  eapply fir_cons_int; [exact HInt_v3|].
  eapply fir_cons_nonint; [exact HNon_v4|].
  eapply fir_cons_nonint; [exact HNon_v5|].
  eapply fir_cons_nonint; [exact HNon_v6|].
  eapply fir_cons_nonint; [exact HNon_v7|].
  eapply fir_cons_nonint; [exact HNon_v8|].
  eapply fir_cons_nonint; [exact HNon_v9|].
  eapply fir_cons_nonint; [exact HNon_v10|].
  eapply fir_cons_nonint; [exact HNon_v11|].
  constructor.
Qed.