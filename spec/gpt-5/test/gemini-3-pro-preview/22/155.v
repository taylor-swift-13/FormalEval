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

Parameter val_2 val_1 val_str val_list val_dict : Any.
Parameter int_2 int_1 : int.

Axiom is_int_2 : IsInt val_2 int_2.
Axiom is_int_1 : IsInt val_1 int_1.
Axiom not_int_str : forall n, ~ IsInt val_str n.
Axiom not_int_list : forall n, ~ IsInt val_list n.
Axiom not_int_dict : forall n, ~ IsInt val_dict n.

Example test_filter_integers_mixed : 
  filter_integers_spec [val_2; val_1; val_str; val_list; val_dict] [int_2; int_1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply is_int_2.
  apply fir_cons_int. apply is_int_1.
  apply fir_cons_nonint. apply not_int_str.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_cons_nonint. apply not_int_dict.
  apply fir_nil.
Qed.