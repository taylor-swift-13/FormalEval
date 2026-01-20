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
Parameter i1 i5 : int.
Axiom HIsInt_v1_i1 : IsInt v1 i1.
Axiom HNotInt_v2 : forall n, ~ IsInt v2 n.
Axiom HIsInt_v3_i5 : IsInt v3 i5.
Axiom HNotInt_v4 : forall n, ~ IsInt v4 n.
Axiom HNotInt_v5 : forall n, ~ IsInt v5 n.
Axiom HNotInt_v6 : forall n, ~ IsInt v6 n.
Axiom HNotInt_v7 : forall n, ~ IsInt v7 n.
Axiom HNotInt_v8 : forall n, ~ IsInt v8 n.
Axiom HNotInt_v9 : forall n, ~ IsInt v9 n.

Example test_case_mixed_integers: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [i1; i5].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply HIsInt_v1_i1 |].
  eapply fir_cons_nonint; [apply HNotInt_v2 |].
  eapply fir_cons_int; [apply HIsInt_v3_i5 |].
  eapply fir_cons_nonint; [apply HNotInt_v4 |].
  eapply fir_cons_nonint; [apply HNotInt_v5 |].
  eapply fir_cons_nonint; [apply HNotInt_v6 |].
  eapply fir_cons_nonint; [apply HNotInt_v7 |].
  eapply fir_cons_nonint; [apply HNotInt_v8 |].
  eapply fir_cons_nonint; [apply HNotInt_v9 |].
  constructor.
Qed.