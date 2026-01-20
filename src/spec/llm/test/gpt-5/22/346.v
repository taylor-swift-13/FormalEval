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

Parameter int_one : int.
Notation "1%Z" := int_one.

Parameter v_1 : Any.
Parameter v_dict_three : Any.
Parameter v_list_455 : Any.
Parameter v_list_big1 : Any.
Parameter v_list_big2 : Any.
Parameter v_list_455b : Any.
Parameter v_empty_dict : Any.

Axiom v_1_is_int : IsInt v_1 1%Z.
Axiom v_dict_three_non : forall n, ~ IsInt v_dict_three n.
Axiom v_list_455_non : forall n, ~ IsInt v_list_455 n.
Axiom v_list_big1_non : forall n, ~ IsInt v_list_big1 n.
Axiom v_list_big2_non : forall n, ~ IsInt v_list_big2 n.
Axiom v_list_455b_non : forall n, ~ IsInt v_list_455b n.
Axiom v_empty_dict_non : forall n, ~ IsInt v_empty_dict n.

Example test_case_new:
  filter_integers_spec
    [v_1; v_dict_three; v_list_455; v_list_big1; v_list_big2; v_list_455b; v_empty_dict]
    [1%Z].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v_1 1%Z
           [v_dict_three; v_list_455; v_list_big1; v_list_big2; v_list_455b; v_empty_dict] []).
  - apply v_1_is_int.
  - apply (fir_cons_nonint v_dict_three
             [v_list_455; v_list_big1; v_list_big2; v_list_455b; v_empty_dict] []).
    + apply v_dict_three_non.
    + apply (fir_cons_nonint v_list_455
               [v_list_big1; v_list_big2; v_list_455b; v_empty_dict] []).
      * apply v_list_455_non.
      * apply (fir_cons_nonint v_list_big1
                 [v_list_big2; v_list_455b; v_empty_dict] []).
        -- apply v_list_big1_non.
        -- apply (fir_cons_nonint v_list_big2
                   [v_list_455b; v_empty_dict] []).
           ++ apply v_list_big2_non.
           ++ apply (fir_cons_nonint v_list_455b
                      [v_empty_dict] []).
              ** apply v_list_455b_non.
              ** apply (fir_cons_nonint v_empty_dict [] []).
                 --- apply v_empty_dict_non.
                 --- apply fir_nil.
Qed.