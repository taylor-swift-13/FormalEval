Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Local Open Scope R_scope.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inj : R -> Any.
Axiom inj_not_int : forall r n, ~ IsInt (inj r) n.

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

Example test_filter_integers_reals : filter_integers_spec [inj 2.7; inj 3.0; inj (-4.6); inj 1.5; inj 1.5] [].
Proof.
  unfold filter_integers_spec.
  repeat (apply fir_cons_nonint; [apply inj_not_int | ]).
  apply fir_nil.
Qed.