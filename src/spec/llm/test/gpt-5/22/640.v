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

Parameter d_one_two : Any.
Parameter d_three_list : Any.
Parameter d_empty : Any.
Parameter d_five1 : Any.
Parameter d_five2 : Any.
Parameter d_seven_eight_ieight : Any.

Axiom not_int_d_one_two : forall n, ~ IsInt d_one_two n.
Axiom not_int_d_three_list : forall n, ~ IsInt d_three_list n.
Axiom not_int_d_empty : forall n, ~ IsInt d_empty n.
Axiom not_int_d_five1 : forall n, ~ IsInt d_five1 n.
Axiom not_int_d_five2 : forall n, ~ IsInt d_five2 n.
Axiom not_int_d_seven_eight_ieight : forall n, ~ IsInt d_seven_eight_ieight n.

Example test_case_dicts: filter_integers_spec [d_one_two; d_three_list; d_empty; d_five1; d_five2; d_seven_eight_ieight] [].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_nonint d_one_two [d_three_list; d_empty; d_five1; d_five2; d_seven_eight_ieight] []).
  - exact not_int_d_one_two.
  - apply (fir_cons_nonint d_three_list [d_empty; d_five1; d_five2; d_seven_eight_ieight] []).
    + exact not_int_d_three_list.
    + apply (fir_cons_nonint d_empty [d_five1; d_five2; d_seven_eight_ieight] []).
      * exact not_int_d_empty.
      * apply (fir_cons_nonint d_five1 [d_five2; d_seven_eight_ieight] []).
        -- exact not_int_d_five1.
        -- apply (fir_cons_nonint d_five2 [d_seven_eight_ieight] []).
           ++ exact not_int_d_five2.
           ++ apply (fir_cons_nonint d_seven_eight_ieight [] []).
              ** exact not_int_d_seven_eight_ieight.
              ** apply fir_nil.
Qed.