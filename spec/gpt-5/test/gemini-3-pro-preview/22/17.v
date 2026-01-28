Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inj_R : R -> Any.
Axiom not_IsInt_R : forall r n, ~ IsInt (inj_R r) n.

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

Example test_filter_integers : filter_integers_spec [inj_R 1.5; inj_R 2.7; inj_R 3.0; inj_R (-4.6); inj_R 1.5; inj_R 1.5] [].
Proof.
  unfold filter_integers_spec.
  repeat (apply fir_cons_nonint; [ apply not_IsInt_R | ]).
  apply fir_nil.
Qed.