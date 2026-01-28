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

Parameter val_2 : Any.
Parameter val_false : Any.
Parameter val_3 : Any.
Parameter val_four : Any.
Parameter val_5_5 : Any.
Parameter val_6 : Any.
Parameter val_seven : Any.
Parameter val_8 : Any.
Parameter val_9_0 : Any.

Axiom is_int_2 : IsInt val_2 2%Z.
Axiom not_int_false : forall n, ~ IsInt val_false n.
Axiom is_int_3 : IsInt val_3 3%Z.
Axiom not_int_four : forall n, ~ IsInt val_four n.
Axiom not_int_5_5 : forall n, ~ IsInt val_5_5 n.
Axiom is_int_6 : IsInt val_6 6%Z.
Axiom not_int_seven : forall n, ~ IsInt val_seven n.
Axiom not_int_8 : forall n, ~ IsInt val_8 n.
Axiom not_int_9_0 : forall n, ~ IsInt val_9_0 n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [val_2; val_false; val_2; val_3; val_four; val_3; val_5_5; val_6; val_seven; val_8; val_9_0; val_8] 
    [2%Z; 2%Z; 3%Z; 3%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n:=2%Z). apply is_int_2.
  apply fir_cons_nonint. apply not_int_false.
  apply fir_cons_int with (n:=2%Z). apply is_int_2.
  apply fir_cons_int with (n:=3%Z). apply is_int_3.
  apply fir_cons_nonint. apply not_int_four.
  apply fir_cons_int with (n:=3%Z). apply is_int_3.
  apply fir_cons_nonint. apply not_int_5_5.
  apply fir_cons_int with (n:=6%Z). apply is_int_6.
  apply fir_cons_nonint. apply not_int_seven.
  apply fir_cons_nonint. apply not_int_8.
  apply fir_cons_nonint. apply not_int_9_0.
  apply fir_cons_nonint. apply not_int_8.
  apply fir_nil.
Qed.