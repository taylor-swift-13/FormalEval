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

Parameter d_empty1 d_empty2 d_three d_floats d_empty3 d_empty4 : Any.
Axiom NonInt_d_empty1 : forall n, ~ IsInt d_empty1 n.
Axiom NonInt_d_empty2 : forall n, ~ IsInt d_empty2 n.
Axiom NonInt_d_three : forall n, ~ IsInt d_three n.
Axiom NonInt_d_floats : forall n, ~ IsInt d_floats n.
Axiom NonInt_d_empty3 : forall n, ~ IsInt d_empty3 n.
Axiom NonInt_d_empty4 : forall n, ~ IsInt d_empty4 n.

Example test_case_new: filter_integers_spec [d_empty1; d_empty2; d_three; d_floats; d_empty3; d_empty4] [].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_nonint d_empty1 [d_empty2; d_three; d_floats; d_empty3; d_empty4] []).
  - apply NonInt_d_empty1.
  - apply (fir_cons_nonint d_empty2 [d_three; d_floats; d_empty3; d_empty4] []).
    + apply NonInt_d_empty2.
    + apply (fir_cons_nonint d_three [d_floats; d_empty3; d_empty4] []).
      * apply NonInt_d_three.
      * apply (fir_cons_nonint d_floats [d_empty3; d_empty4] []).
        -- apply NonInt_d_floats.
        -- apply (fir_cons_nonint d_empty3 [d_empty4] []).
           ++ apply NonInt_d_empty3.
           ++ apply (fir_cons_nonint d_empty4 [] []).
              ** apply NonInt_d_empty4.
              ** constructor.
Qed.