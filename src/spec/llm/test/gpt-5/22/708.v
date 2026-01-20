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

Parameter v0 v1 v2 v3 v4 v5 v6 : Any.
Axiom v0_is_int : IsInt v0 0%Z.
Axiom v1_nonint : forall n:int, ~ IsInt v1 n.
Axiom v2_nonint : forall n:int, ~ IsInt v2 n.
Axiom v3_nonint : forall n:int, ~ IsInt v3 n.
Axiom v4_nonint : forall n:int, ~ IsInt v4 n.
Axiom v5_nonint : forall n:int, ~ IsInt v5 n.
Axiom v6_nonint : forall n:int, ~ IsInt v6 n.

Example test_case: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6] [0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v0_is_int |].
  eapply fir_cons_nonint; [apply v1_nonint |].
  eapply fir_cons_nonint; [apply v2_nonint |].
  eapply fir_cons_nonint; [apply v3_nonint |].
  eapply fir_cons_nonint; [apply v4_nonint |].
  eapply fir_cons_nonint; [apply v5_nonint |].
  eapply fir_cons_nonint; [apply v6_nonint |].
  constructor.
Qed.