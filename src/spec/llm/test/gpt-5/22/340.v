Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.
Axiom v1_isint : IsInt v1 1%Z.
Axiom v2_isint : IsInt v2 (-8)%Z.
Axiom v3_isint : IsInt v3 4%Z.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom v7_nonint : forall n, ~ IsInt v7 n.
Axiom v8_isint : IsInt v8 31%Z.
Axiom v9_isint : IsInt v9 0%Z.
Axiom v10_nonint : forall n, ~ IsInt v10 n.

Example test_case_complex: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [1%Z; -8%Z; 4%Z; 31%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact v1_isint |].
  eapply fir_cons_int; [exact v2_isint |].
  eapply fir_cons_int; [exact v3_isint |].
  eapply fir_cons_nonint; [exact v4_nonint |].
  eapply fir_cons_nonint; [exact v5_nonint |].
  eapply fir_cons_nonint; [exact v6_nonint |].
  eapply fir_cons_nonint; [exact v7_nonint |].
  eapply fir_cons_int; [exact v8_isint |].
  eapply fir_cons_int; [exact v9_isint |].
  eapply fir_cons_nonint; [exact v10_nonint |].
  constructor.
Qed.