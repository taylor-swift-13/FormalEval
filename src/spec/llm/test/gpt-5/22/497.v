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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Any.
Parameter oneZ fourZ : int.
Axiom IsInt_v1 : IsInt v1 oneZ.
Axiom NonInt_v2 : forall n, ~ IsInt v2 n.
Axiom IsInt_v3 : IsInt v3 fourZ.
Axiom NonInt_v4 : forall n, ~ IsInt v4 n.
Axiom NonInt_v5 : forall n, ~ IsInt v5 n.
Axiom NonInt_v6 : forall n, ~ IsInt v6 n.
Axiom NonInt_v7 : forall n, ~ IsInt v7 n.
Axiom NonInt_v8 : forall n, ~ IsInt v8 n.
Axiom NonInt_v9 : forall n, ~ IsInt v9 n.
Axiom IsInt_v10 : IsInt v10 oneZ.
Axiom NonInt_v11 : forall n, ~ IsInt v11 n.

Notation "1%Z" := oneZ.
Notation "4%Z" := fourZ.

Example test_case_nonempty: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] [1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v1 |].
  eapply fir_cons_nonint; [apply NonInt_v2 |].
  eapply fir_cons_int; [apply IsInt_v3 |].
  eapply fir_cons_nonint; [apply NonInt_v4 |].
  eapply fir_cons_nonint; [apply NonInt_v5 |].
  eapply fir_cons_nonint; [apply NonInt_v6 |].
  eapply fir_cons_nonint; [apply NonInt_v7 |].
  eapply fir_cons_nonint; [apply NonInt_v8 |].
  eapply fir_cons_nonint; [apply NonInt_v9 |].
  eapply fir_cons_int; [apply IsInt_v10 |].
  eapply fir_cons_nonint; [apply NonInt_v11 |].
  constructor.
Qed.