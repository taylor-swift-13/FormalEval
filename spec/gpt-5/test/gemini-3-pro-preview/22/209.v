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

Parameter val_false : Any.
Parameter val_None : Any.
Parameter val_float1 : Any.
Parameter val_int5 : Any.
Parameter val_list1 : Any.
Parameter val_intNeg7 : Any.
Parameter val_int0 : Any.
Parameter val_strA : Any.
Parameter val_strB : Any.
Parameter val_list2 : Any.
Parameter val_float2 : Any.
Parameter val_dict1 : Any.
Parameter val_dict2 : Any.
Parameter val_intNeg8 : Any.
Parameter val_list3 : Any.

Parameter n5 : int.
Parameter nNeg7 : int.
Parameter n0 : int.
Parameter nNeg8 : int.

Axiom is_int_5 : IsInt val_int5 n5.
Axiom is_int_neg7 : IsInt val_intNeg7 nNeg7.
Axiom is_int_0 : IsInt val_int0 n0.
Axiom is_int_neg8 : IsInt val_intNeg8 nNeg8.

Axiom not_int_false : forall n, ~ IsInt val_false n.
Axiom not_int_None : forall n, ~ IsInt val_None n.
Axiom not_int_float1 : forall n, ~ IsInt val_float1 n.
Axiom not_int_list1 : forall n, ~ IsInt val_list1 n.
Axiom not_int_strA : forall n, ~ IsInt val_strA n.
Axiom not_int_strB : forall n, ~ IsInt val_strB n.
Axiom not_int_list2 : forall n, ~ IsInt val_list2 n.
Axiom not_int_float2 : forall n, ~ IsInt val_float2 n.
Axiom not_int_dict1 : forall n, ~ IsInt val_dict1 n.
Axiom not_int_dict2 : forall n, ~ IsInt val_dict2 n.
Axiom not_int_list3 : forall n, ~ IsInt val_list3 n.

Example test_filter_integers : filter_integers_spec 
  [val_false; val_false; val_None; val_float1; val_int5; val_list1; val_intNeg7; val_int0; val_strA; val_strB; val_list2; val_float2; val_dict1; val_dict2; val_intNeg8; val_list3; val_list1; val_int5; val_list1]
  [n5; nNeg7; n0; nNeg8; n5].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_false.
  apply fir_cons_nonint. apply not_int_false.
  apply fir_cons_nonint. apply not_int_None.
  apply fir_cons_nonint. apply not_int_float1.
  apply fir_cons_int. apply is_int_5.
  apply fir_cons_nonint. apply not_int_list1.
  apply fir_cons_int. apply is_int_neg7.
  apply fir_cons_int. apply is_int_0.
  apply fir_cons_nonint. apply not_int_strA.
  apply fir_cons_nonint. apply not_int_strB.
  apply fir_cons_nonint. apply not_int_list2.
  apply fir_cons_nonint. apply not_int_float2.
  apply fir_cons_nonint. apply not_int_dict1.
  apply fir_cons_nonint. apply not_int_dict2.
  apply fir_cons_int. apply is_int_neg8.
  apply fir_cons_nonint. apply not_int_list3.
  apply fir_cons_nonint. apply not_int_list1.
  apply fir_cons_int. apply is_int_5.
  apply fir_cons_nonint. apply not_int_list1.
  apply fir_nil.
Qed.