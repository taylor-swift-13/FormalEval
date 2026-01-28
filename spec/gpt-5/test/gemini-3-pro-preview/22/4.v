Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
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

Example test_filter_integers_simple (v1 v2 v3 v4 v5 : Any) :
  IsInt v1 1 ->
  IsInt v2 2 ->
  IsInt v3 3 ->
  IsInt v4 4 ->
  IsInt v5 5 ->
  filter_integers_spec [v1; v2; v3; v4; v5] [1; 2; 3; 4; 5].
Proof.
  intros H1 H2 H3 H4 H5.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1). exact H1.
  apply fir_cons_int with (n := 2). exact H2.
  apply fir_cons_int with (n := 3). exact H3.
  apply fir_cons_int with (n := 4). exact H4.
  apply fir_cons_int with (n := 5). exact H5.
  apply fir_nil.
Qed.