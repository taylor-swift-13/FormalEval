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

Parameter v1 : Any.
Parameter v2 : Any.
Parameter v3_str : Any.
Parameter v4 : Any.
Parameter v5_float : Any.
Parameter v6_list : Any.
Parameter v7_dict : Any.
Parameter v8_bool : Any.
Parameter v9_bool : Any.

Axiom v1_is_int : IsInt v1 1.
Axiom v2_is_int : IsInt v2 2.
Axiom v3_not_int : forall n, ~ IsInt v3_str n.
Axiom v4_is_int : IsInt v4 4.
Axiom v5_not_int : forall n, ~ IsInt v5_float n.
Axiom v6_not_int : forall n, ~ IsInt v6_list n.
Axiom v7_not_int : forall n, ~ IsInt v7_dict n.
Axiom v8_not_int : forall n, ~ IsInt v8_bool n.
Axiom v9_not_int : forall n, ~ IsInt v9_bool n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [v1; v2; v3_str; v4; v5_float; v6_list; v7_dict; v8_bool; v9_bool] 
    [1; 2; 4].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1); [apply v1_is_int |].
  apply fir_cons_int with (n := 2); [apply v2_is_int |].
  apply fir_cons_nonint; [apply v3_not_int |].
  apply fir_cons_int with (n := 4); [apply v4_is_int |].
  apply fir_cons_nonint; [apply v5_not_int |].
  apply fir_cons_nonint; [apply v6_not_int |].
  apply fir_cons_nonint; [apply v7_not_int |].
  apply fir_cons_nonint; [apply v8_not_int |].
  apply fir_cons_nonint; [apply v9_not_int |].
  apply fir_nil.
Qed.