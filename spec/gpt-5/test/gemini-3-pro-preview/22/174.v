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

Parameter val_1 : Any.
Parameter val_l23 : Any.
Parameter val_4 : Any.
Parameter val_l5 : Any.
Parameter val_nil : Any.
Parameter val_l78 : Any.
Parameter val_s9 : Any.
Parameter val_dict : Any.

Axiom is_int_val_1 : IsInt val_1 1%Z.
Axiom is_int_val_4 : IsInt val_4 4%Z.
Axiom not_int_val_l23 : forall n, ~ IsInt val_l23 n.
Axiom not_int_val_l5 : forall n, ~ IsInt val_l5 n.
Axiom not_int_val_nil : forall n, ~ IsInt val_nil n.
Axiom not_int_val_l78 : forall n, ~ IsInt val_l78 n.
Axiom not_int_val_s9 : forall n, ~ IsInt val_s9 n.
Axiom not_int_val_dict : forall n, ~ IsInt val_dict n.

Example test_filter_integers : 
  filter_integers_spec 
    [val_1; val_l23; val_4; val_l5; val_nil; val_l78; val_s9; val_s9; val_dict; val_1] 
    [1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply is_int_val_1.
  apply fir_cons_nonint. apply not_int_val_l23.
  apply fir_cons_int. apply is_int_val_4.
  apply fir_cons_nonint. apply not_int_val_l5.
  apply fir_cons_nonint. apply not_int_val_nil.
  apply fir_cons_nonint. apply not_int_val_l78.
  apply fir_cons_nonint. apply not_int_val_s9.
  apply fir_cons_nonint. apply not_int_val_s9.
  apply fir_cons_nonint. apply not_int_val_dict.
  apply fir_cons_int. apply is_int_val_1.
  apply fir_nil.
Qed.