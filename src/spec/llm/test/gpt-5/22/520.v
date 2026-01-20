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

Parameters v1 v2 v3 v4 v5 v6 v7 : Any.
Axiom v1_is_int : IsInt v1 1%Z.
Axiom v2_not_int : forall n, ~ IsInt v2 n.
Axiom v3_not_int : forall n, ~ IsInt v3 n.
Axiom v4_not_int : forall n, ~ IsInt v4 n.
Axiom v5_is_int : IsInt v5 64%Z.
Axiom v6_not_int : forall n, ~ IsInt v6 n.
Axiom v7_is_int : IsInt v7 7%Z.

Example test_case_nested: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [1%Z; 64%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact v1_is_int |].
  eapply fir_cons_nonint; [exact v2_not_int |].
  eapply fir_cons_nonint; [exact v3_not_int |].
  eapply fir_cons_nonint; [exact v4_not_int |].
  eapply fir_cons_int; [exact v5_is_int |].
  eapply fir_cons_nonint; [exact v6_not_int |].
  eapply fir_cons_int; [exact v7_is_int |].
  constructor.
Qed.